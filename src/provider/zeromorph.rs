// ZeroMorph

use halo2curves::bn256::{
    G1, G1Affine, G2, Fr,
};
use std::ops::{Mul};
use ff::Field;
use crate::provider::kzg::KZGParams;
use crate::provider::kzg::KZGScheme;

#[derive(Clone)]
pub struct ZeroMorphParams {
    pub nmax: u64,
    pub gen1: G1,
    pub gen2: G2,
    pub powers_of_tau: Vec<G1Affine>,
    pub xi1: G1,
    pub xi2: G2,
    pub tau2: G2,
    pub kzg: KZGParams,
}

#[derive(Clone)]
pub struct ZeroMorphProof {
    pub pi: G1,
    pub delta: G1,
}


pub trait ZeroMorphScheme {
    fn setup(nmax: u64) -> Self;
    fn commit(&self, p: &[Fr]) -> (G1, Fr);
    fn open(&self, C: G1, r: Fr, p: &[Fr]) -> bool;
    fn eval(&self, q: &[Fr]) -> G1;
    fn proveEval(&self, f: &[Fr], v: Fr, u: &[Fr], r: Fr) -> ZeroMorphProof;
    fn verifyEval(&self, C: G1, v: Fr, u: &[Fr], proof: ZeroMorphProof) -> bool;
}


impl ZeroMorphScheme for ZeroMorphParams {

    fn setup(nmax: u64) -> ZeroMorphParams {

        let kzg = KZGParams::setup(nmax);

        // FIXME: avoid repeated code
        let rng = &mut rand::thread_rng();
        let tau = Fr::random(rng);
        let rng = &mut rand::thread_rng();
        let xi = Fr::random(rng);

        let gen1: G1 = G1::generator();
        let gen2: G2 = G2::generator();
        let mut powers = Vec::new();
        let mut xi1 = gen1;
        let mut xi2 = gen2;
        let mut tau2 = gen2;

        for i in 0..nmax {
            let gtau = gen1;
            let result = gtau.mul(tau.pow([i as u64]));
            powers.push(result.into());
            xi1 = gen1.mul(xi);
            xi2 = gen2.mul(xi);
            tau2 = gen2.mul(tau);
        }
        ZeroMorphParams{
            nmax,
            gen2: gen2.into(),
            gen1: gen1.into(),
            powers_of_tau: powers,
            xi1,
            xi2,
            tau2,
            kzg,
        }
    }

    /// Commit to univariate polynomial p given in coefficient representation
    fn commit(&self, p: &[Fr]) -> (G1, Fr) {
        self.kzg.commit(p)
    }

    /// Open the KZG commitment
    fn open(&self, C: G1, r: Fr, p: &[Fr]) -> bool {
        self.kzg.open(C, r, p)
    }

    /// Use power of tau to compute evaluation of polynomial q in coefficient representation.
    fn eval(&self, q: &[Fr]) -> G1 {
        self.kzg.eval(q)
    }

    #[allow(unused_variables)]
    /// Prove evaluation of f at point u is equal to v.
    fn proveEval(&self, f: &[Fr], v: Fr, u: &[Fr], r: Fr) -> ZeroMorphProof {
        todo!()
    }

    #[allow(unused_variables)]
    /// Verify proof that polynomial in commitment C evals to v at point u.
    fn verifyEval(&self, C: G1, v: Fr, u: &[Fr], proof: ZeroMorphProof) -> bool {
        todo!()
    }

}

#[test]
fn test_zm_open(){
    let zm = ZeroMorphParams::setup(3);
    let p = [Fr::from(0), Fr::from(0), Fr::from(1)];
    let (C, r) = zm.commit(&p);
    assert!(zm.open(C, r, &p));
}


#[test]
fn test_zm_simple(){
    let zm = ZeroMorphParams::setup(3);
    let p = [Fr::from(0), Fr::from(0), Fr::from(1)]; // this is X_1
    let (C, r) = zm.commit(&p);
    let v = Fr::from(1);
    let u0 = Fr::from(0);
    let u1 = Fr::from(1);
    // X1 - 1 = (X1 - 1).1, we have q=1
    let proof = zm.proveEval(&p, v, &[u0, u1], r);
    let b = zm.verifyEval(C, v, &[u0, u1], proof.clone());
    assert!(b);
}

