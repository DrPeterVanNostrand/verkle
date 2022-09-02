use ff::PrimeField;
use group::GroupEncoding;
use halo2_proofs::{
    arithmetic::{best_multiexp, lagrange_interpolate},
    pasta::{Eq, EqAffine, Fp},
    poly::commitment::Params,
};
use sha2::{Digest, Sha256};

// Vesta
type F = Fp;
type C = Eq;
type Affine = EqAffine;

// Create Pedersen vector commitment params for vectors of len `n`.
#[inline]
fn gen_pedersen_params(n: usize) -> Vec<Affine> {
    assert!(n.is_power_of_two());
    // `n = 2^k``.
    let k = n.trailing_zeros();
    Params::new(k).get_g()
}

// Pedersen vector commitment.
#[inline]
fn vec_commit(v: &[F], bases: &[Affine]) -> C {
    best_multiexp(v, bases)
}

// Hash Pedersen commitment from curve to scalar field.
fn hash_commit(commit: &C) -> F {
    let preimage = commit.to_bytes();
    let digest = Sha256::digest(&preimage);
    let mut digest_repr = <F as PrimeField>::Repr::default();
    digest_repr.as_mut().copy_from_slice(&digest);
    digest_repr[31] &= 0b00111111;
    F::from_repr(digest_repr).unwrap()
}

// Each non-leaf tree node is a polynomial and commitment to its coefficients.
struct NonLeafNode<const A: usize> {
    poly_coeffs: Vec<F>,
    commit: C,
    commit_digest: F,
}

struct VerkleTree<const A: usize> {
    leafs: Vec<F>,
    non_leaf_layers: Vec<Vec<NonLeafNode<A>>>,
    root: C,
}

impl<const A: usize> VerkleTree<A> {
    fn new(leafs: Vec<F>, pedersen_bases: &[Affine]) -> Self {
        let num_leafs = leafs.len();

        assert!(A.is_power_of_two() && A != 1);
        assert!(num_leafs.is_power_of_two() && num_leafs >= A);
        assert_eq!(pedersen_bases.len(), A);

        let log2_arity = A.trailing_zeros() as usize;
        let log2_leafs = num_leafs.trailing_zeros() as usize;
        let height = log2_leafs / log2_arity;

        let interp_domain: Vec<F> = (0..A as u64).map(F::from).collect();

        let mut cur_layer_len = num_leafs;
        let mut non_leaf_layers = Vec::<Vec<NonLeafNode<A>>>::with_capacity(height);

        for h in 0..height {
            let next_layer_len = cur_layer_len >> log2_arity;
            let mut next_layer = Vec::<NonLeafNode<A>>::with_capacity(next_layer_len);

            if h == 0 {
                for sibs in leafs.chunks(A) {
                    let poly_coeffs = lagrange_interpolate(&interp_domain, sibs);
                    assert_eq!(poly_coeffs.len(), A);
                    let commit = vec_commit(&poly_coeffs, pedersen_bases);
                    let commit_digest = hash_commit(&commit);
                    next_layer.push(NonLeafNode {
                        poly_coeffs,
                        commit,
                        commit_digest,
                    });
                }
            } else {
                for sibs in non_leaf_layers.last().unwrap().chunks(A) {
                    let sibs: Vec<F> = sibs.iter().map(|sib| sib.commit_digest).collect();
                    let poly_coeffs = lagrange_interpolate(&interp_domain, &sibs);
                    assert_eq!(poly_coeffs.len(), A);
                    let commit = vec_commit(&poly_coeffs, pedersen_bases);
                    let commit_digest = hash_commit(&commit);
                    next_layer.push(NonLeafNode {
                        poly_coeffs,
                        commit,
                        commit_digest,
                    });
                }
            }

            non_leaf_layers.push(next_layer);
            cur_layer_len = next_layer_len;
        }

        let root = non_leaf_layers[height - 1][0].commit;

        VerkleTree {
            leafs,
            non_leaf_layers,
            root,
        }
    }

    fn root(&self) -> &C {
        &self.root
    }

    fn prove(&self, mut challenge: usize) -> VerkleProof<A> {
        assert!(challenge < self.leafs.len());
        let leaf = self.leafs[challenge];
        let polys = self.non_leaf_layers
            .iter()
            .map(|layer| {
                challenge /= A;
                layer[challenge].poly_coeffs.to_vec()
            })
            .collect::<Vec<Vec<F>>>();
        VerkleProof {
            leaf,
            polys,
        }
    }
}

#[inline]
fn eval_poly(coeffs: &[F], x: F) -> F {
    let mut x_pow = x;
    coeffs
        .iter()
        .skip(1)
        .fold(coeffs[0], |mut acc, coeff| {
            acc += coeff * x_pow;
            x_pow *= x;
            acc
        })
}

#[derive(Debug)]
struct VerkleProof<const A: usize> {
    leaf: F,
    polys: Vec<Vec<F>>,
}

impl<const A: usize> VerkleProof<A> {
    fn verify(&self, mut challenge: usize, root: &C, pedersen_bases: &[Affine]) -> bool {
        let arity_bit_len = A.trailing_zeros() as usize;
        
        // Check `poly_0(X)` evaluates to provided leaf.
        let mut x = F::from((challenge % A) as u64);
        let mut y = eval_poly(&self.polys[0], x);
        if y != self.leaf {
            println!("error: poly_0(x) != leaf");
            return false;
        }
        let mut commit = vec_commit(&self.polys[0], pedersen_bases);

        // Check `poly_i(X)` evaluates to the previous polynomial's commitment digest.
        let mut height = 1;
        for poly in &self.polys[1..] {
            let commit_digest = hash_commit(&commit);
            challenge >>= arity_bit_len;
            x = F::from((challenge % A) as u64);
            y = eval_poly(poly, x);
            if y != commit_digest {
                println!("error: poly_{}(x) != commit(poly_{})", height, height - 1);
                return false;
            }
            commit = vec_commit(poly, pedersen_bases);
            height += 1;
        }

        commit == *root
    }
}

fn main() {
    #[cfg(feature = "bench")]
    use std::time::Instant;

    // Tree arity.
    const A: usize = 2;
    #[cfg(feature = "bench")]
    type ARITY = typenum::U2;
    const NUM_LEAFS: usize = 8;
    const CHALLENGE: usize = 7;

    let pedersen_bases = gen_pedersen_params(A);

    let leafs: Vec<F> = (0..NUM_LEAFS as u64).map(F::from).collect();
    #[cfg(feature = "bench")]
    let start = Instant::now();
    let tree = VerkleTree::<A>::new(leafs, &pedersen_bases);
    #[cfg(feature = "bench")]
    let vtree_build_time = start.elapsed().as_secs_f32();
    let root = tree.root();

    // Good proof.
    let mut proof = tree.prove(CHALLENGE);
    let is_valid = proof.verify(CHALLENGE, root, &pedersen_bases);
    dbg!(is_valid);

    // Bad proof.
    proof.polys[0][0] += F::one();
    let is_valid = proof.verify(CHALLENGE, root, &pedersen_bases);
    dbg!(is_valid);

    // Bechmark verkle tree building against sha256 and poseidon merkle tree building.
    #[cfg(feature = "bench")]
    {
        let mut layer_len = NUM_LEAFS;
        let start = Instant::now();
        while layer_len > 1 {
            layer_len /= A;
            for _ in 0..layer_len {
                Sha256::digest(&[0u8; 32 * A]);
            }
        }
        let sha256_build_time = start.elapsed().as_secs_f32();

        use neptune::poseidon::{Poseidon, PoseidonConstants};
        let consts = PoseidonConstants::<F, ARITY>::new();
        let mut hasher = Poseidon::<F, ARITY>::new_with_preimage(&[F::zero(); A], &consts);
        let mut layer_len = NUM_LEAFS;
        let start = Instant::now();
        while layer_len > 1 {
            layer_len /= A;
            for _ in 0..layer_len {
                hasher.hash();
                hasher.reset();
            }
        }
        let poseidon_build_time = start.elapsed().as_secs_f32();

        dbg!(vtree_build_time);
        dbg!(sha256_build_time);
        dbg!(poseidon_build_time);
    };
}
