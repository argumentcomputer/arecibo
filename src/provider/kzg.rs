// KZG

use halo2curves::bn256::{
    G1, G1Affine, G2, G2Affine, Fr,
};
use std::ops::{Mul, Sub};
use crate::provider::cpu_best_multiexp;
use ff::Field;
use std::ops::Add;
use halo2curves::bn256::Bn256;
use halo2curves::pairing::Engine;
use pasta_curves::group::Group;

#[derive(Clone)]
pub struct KZGParams {
    pub nmax: u64,
    pub gen1: G1,
    pub gen2: G2,
    pub powers_of_tau: Vec<G1Affine>,
    pub xi1: G1,
    pub xi2: G2,
    pub tau2: G2,
}

#[derive(Clone)]
pub struct KZGProof {
    pub pi: G1,
    pub delta: G1,
}

pub trait KZGScheme {
    fn setup(nmax: u64) -> Self;
    fn commit(&self, p: &[Fr]) -> (G1, Fr);
    fn open(&self, C: G1, r: Fr, p: &[Fr]) -> bool;
    fn eval(&self, q: &[Fr]) -> G1;
    fn proveEval(&self, f: &[Fr], v: Fr, u: Fr, r: Fr) -> KZGProof;
    fn verifyEval(&self, C: G1, v: Fr, u: Fr, proof: KZGProof) -> bool;
}


fn init(f: &[Fr]) -> Vec<Fr> {
    let mut fmv = vec!(Fr::from(0); f.len());
    for (i, elem) in f.iter().enumerate() {
        fmv[i] = *elem;
    }
    fmv
}

fn compute_q(f: &[Fr], v: Fr, u: Fr) -> Vec<Fr> {
    let mut q = vec!(Fr::from(0); f.len());
    let mut xmu = vec!(Fr::from(0); f.len());
    // f - v
    let mut fmv = init(f);
    fmv[0] = fmv[0].sub(&v);

    // X - u
    xmu[1] = Fr::from(1);
    xmu[0] = xmu[0].sub(&u);

    // (f - v) / (X - u)
    // for each coeff,i in f.reverse, multiply (X - u) by coeff.Xˆ(i-1) and subtract from (f - v)
    let mut remainder = vec!(Fr::from(0); f.len());
    for (i, elem) in fmv.iter().enumerate() {
        remainder[i] = *elem;
    }
    let mut i = fmv.len()-1;
    while i > 0 {
        let coeff = remainder[i];
        // remainder = fvm - (X - u).coeff.Xˆ(i-1)
        remainder[i] = remainder[i].sub(&coeff);
        assert_eq!(remainder[i], Fr::from(0));
        remainder[i-1] = remainder[i-1].add(coeff.mul(u));
        // q += coeff.Xˆ(i-1)
        q[i-1] += coeff;
        i -= 1;
    }
    assert_eq!(remainder[0], Fr::from(0));
    q
}


impl KZGScheme for KZGParams {

    fn setup(nmax: u64) -> Self {

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
        KZGParams{
            nmax,
            gen2: gen2.into(),
            gen1: gen1.into(),
            powers_of_tau: powers,
            xi1,
            xi2,
            tau2,
        }
    }

    /// Commit to univariate polynomial p given in coefficient representation
    fn commit(&self, p: &[Fr]) -> (G1, Fr) {

        let rng = &mut rand::thread_rng();
        let r = Fr::random(rng);

        // MSM
        let mut C = cpu_best_multiexp(p, &self.powers_of_tau);

        // compute r.xi
        let rxi = self.xi1.mul(r);

        // add r
        C = C.add(rxi);

        (C, r)
    }


    /// Open polynomial commitment
    fn open(&self, C: G1, r: Fr, p: &[Fr]) -> bool {

        // MSM
        let mut recomputedC = cpu_best_multiexp(p, &self.powers_of_tau);

        // compute r.xi
        let rxi = self.xi1.mul(r);

        // add r
        recomputedC = recomputedC.add(rxi);

        let diff = C - recomputedC;

        //C != recomputedC
        diff.is_identity().into()
    }



    /// Use power of tau to compute evaluation of polynomial q in coefficient representation.
    fn eval(&self, q: &[Fr]) -> G1 {
        let mut sum = self.powers_of_tau[0].mul(q[0]);
        for (i, coeff) in q.iter().enumerate().skip(1) {
            let term = self.powers_of_tau[i].mul(coeff);
            sum = sum.add(term);
        }
        sum
    }

    /// Prove evaluation of f at point u is equal to v.
    fn proveEval(&self, f: &[Fr], v: Fr, u: Fr, r: Fr) -> KZGProof {
        let rng = &mut rand::thread_rng();
        let s = Fr::random(rng);

        // compute pi
        let q = compute_q(f, v, u);
        // eval q
        let gqtau = self.eval(&q[..]);


        let sxi1 = self.xi1.mul(s);
        let pi = gqtau.add(sxi1);

        // compute delta
        let mut delta = self.gen1.mul(r);
        delta = delta.sub(self.powers_of_tau[1].mul(s));
        delta = delta.add(self.gen1.mul(s.mul(u)));
        KZGProof { pi, delta }
    }

    /// Verify proof that polynomial in commitment C evals to v at point u.
    fn verifyEval(&self, C: G1, v: Fr, u: Fr, proof: KZGProof) -> bool {
        // pleft
        let vgen1 = self.gen1.mul(v);
        let mut csvgen1 = C;
        csvgen1 = csvgen1.sub(vgen1);
        let g2 = self.gen2;
        let pleft = Bn256::pairing(&G1Affine::from(csvgen1), &G2Affine::from(g2));
        // pright1
        let ug2 = g2.mul(u);
        let tau2mug2 = self.tau2.sub(ug2);
        let pright1 = Bn256::pairing(&G1Affine::from(proof.pi), &G2Affine::from(tau2mug2));

        // pright2
        let pright2 = Bn256::pairing(&G1Affine::from(proof.delta), &G2Affine::from(self.xi2));
        // pleft =? pright1 - pright2
        let r1pr2 = pright1.add(pright2);
        pleft.eq(&r1pr2)
    }
}

#[test]
fn test_kzg_open(){

    let kzg = KZGParams::setup(3);
    //let params = setup(3);
    let p = [Fr::from(0), Fr::from(0), Fr::from(1)]; // this is Xˆ2
    let (C, r) = kzg.commit(&p);
    assert!(kzg.open(C, r, &p));
}


#[test]
fn test_kzg_simple(){

    let kzg = KZGParams::setup(3);
    //let params = setup(3);
    let p = [Fr::from(0), Fr::from(0), Fr::from(1)]; // this is Xˆ2
    let (C, r) = kzg.commit(&p);
    let v = Fr::from(1);
    let u = Fr::from(1);
    // Xˆ2 - 1 = (X + 1).(X - 1)
    let proof = kzg.proveEval(&p, v, u, r);
    let b = kzg.verifyEval(C, v, u, proof.clone());
    assert!(b);
}

#[test]
fn test_kzg_simple2(){
    let kzg = KZGParams::setup(5);
    let p = [Fr::from(0), Fr::from(0), Fr::from(0), Fr::from(0), Fr::from(1)]; // this is Xˆ4
    let (C, r) = kzg.commit(&p);
    let v = Fr::from(1);
    let u = Fr::from(1);
    // Xˆ4 - 1 = (Xˆ2 + 1).(Xˆ2 - 1) = (Xˆ2 + 1).(X + 1).(X - 1)
    let proof = kzg.proveEval(&p, v, u, r);
    let b = kzg.verifyEval(C, v, u, proof.clone());
    assert!(b);
}

#[test]
fn test_kzg_simple3(){
    let kzg = KZGParams::setup(5);
    let p = [Fr::from(1), Fr::from(1), Fr::from(1), Fr::from(1), Fr::from(1)]; // this is Xˆ4 + Xˆ3 + ˆXˆ2 + Xˆ1 + 1
    let (C, r) = kzg.commit(&p);
    let v = Fr::from(5);
    let u = Fr::from(1);
    let proof = kzg.proveEval(&p, v, u, r);
    let b = kzg.verifyEval(C, v, u, proof.clone());
    assert!(b);
}
