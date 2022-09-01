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

struct NonLeafNode<const A: usize> {
    poly_coeffs: Vec<F>,
    commit: C,
    commit_digest: F,
}

fn hash_commit(commit: &C) -> F {
    let preimage = commit.to_bytes();
    let digest = Sha256::digest(&preimage);
    let mut digest_repr = <F as PrimeField>::Repr::default();
    digest_repr.as_mut().copy_from_slice(&digest);
    digest_repr[31] &= 0b00111111;
    F::from_repr(digest_repr).unwrap()
}

struct VerkleTree<const A: usize> {
    pedersen_bases: Vec<Affine>,
    leafs: Vec<F>,
    non_leaf_layers: Vec<Vec<NonLeafNode<A>>>,
}

impl<const A: usize> VerkleTree<A> {
    fn new(leafs: Vec<F>) -> Self {
        let num_leafs = leafs.len();

        assert!(A.is_power_of_two() && A != 1);
        assert!(num_leafs.is_power_of_two() && num_leafs >= A);

        let log2_arity = A.trailing_zeros() as usize;
        let log2_leafs = num_leafs.trailing_zeros() as usize;
        let height = log2_leafs / log2_arity;

        let pedersen_bases = Params::new(log2_arity as u32).get_g();
        assert_eq!(pedersen_bases.len(), A);

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
                    let commit = best_multiexp(&poly_coeffs, &pedersen_bases);
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
                    let commit = best_multiexp(&poly_coeffs, &pedersen_bases);
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

        VerkleTree {
            leafs,
            non_leaf_layers,
            pedersen_bases,
        }
    }

    fn prove(&self, challenge: usize) -> VerkleProof<A> {
        // TODO:
        VerkleProof {
            path: vec![],
        }
    }
}

struct VerkleProof<const A: usize> {
    path: Vec<Vec<F>>,
}

fn main() {
    const A: usize = 2;
    const NUM_LEAFS: usize = 8;

    let leafs = vec![F::zero(); NUM_LEAFS];
    let tree = VerkleTree::<A>::new(leafs);
}
