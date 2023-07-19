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

#[derive(Clone)]
pub struct KZGParams {
    pub nmax: u64,
    pub tau: Fr, // TODO: remove toxic waste! q(tau) must be computed using power of tau
    pub powers_of_tau: Vec<G1Affine>,
    pub xi1: G1Affine,
    pub gen2: G2Affine,
    pub xi2: G2Affine,
    pub tau2: G2Affine,
}

#[derive(Clone)]
pub struct KZGProof {
    pub pi: G1Affine,
    pub delta: G1Affine,
}

pub fn setup(nmax: u64) -> KZGParams {

    let rng = &mut rand::thread_rng();
    let tau = Fr::random(rng);
    //let tau = Fr::from(1);
    let rng = &mut rand::thread_rng();
    let xi = Fr::random(rng);

    let mut powers = Vec::new();
    let mut xi1 = G1::generator();
    let mut xi2 = G2::generator();
    let mut tau2 = G2::generator();
    let gen1 = G1::generator();
    let gen2 = G2::generator();
    for i in 0..nmax {

        let gtau = gen1;
        let result = gtau.mul(tau.pow([i as u64]));

        powers.push(result.into());
        xi1 = gen1.mul(xi).into();
        xi2 = gen2.mul(xi).into();

        tau2 = gen2.mul(tau).into();
    }
    let res: KZGParams = KZGParams{
        nmax,
        tau,
        powers_of_tau: powers,
        xi1: xi1.into(),
        gen2: gen2.into(),
        xi2: xi2.into(),
        tau2: tau2.into(),
    };
    return res;
}

pub fn commit(p: &[Fr], params: KZGParams) -> (G1, Fr) {

    let rng = &mut rand::thread_rng();
    let r = Fr::random(rng);

    // MSM
    let mut C = cpu_best_multiexp(p, &params.powers_of_tau);

    // compute r.xi
    let rxi = params.xi1.mul(r);

    // add r
    C = C.add(rxi);

    (C, r)
}

fn compute_q_helper(f: &[Fr], v: Fr, u: Fr) -> Vec<Fr> {
    let mut q = vec!(Fr::from(0); f.len());
    let mut xmu = vec!(Fr::from(0); f.len());
    // f - v
    let mut fmv = vec!(Fr::from(0); f.len());
    for (i, elem) in f.iter().enumerate() {
        fmv[i] = *elem;
    }
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

fn eval(q: &[Fr], tau: Fr) -> Fr {
    let mut ptau = Fr::from(1);
    let mut sum = Fr::from(0);
    for coeff in q.iter() {
        let term = coeff.mul(&ptau);
        ptau *= tau;
        sum += term;
    }
    sum
}

pub fn proveEval(f: &[Fr], v: Fr, u: Fr, r: Fr, params: KZGParams) -> KZGProof {
    let rng = &mut rand::thread_rng();
    let s = Fr::random(rng);

    let q = compute_q_helper(f, v, u);
    // eval q
    let qtau = eval(&q[..], params.tau);

    let gen1 = G1::generator();
    let gqtau = gen1.mul(qtau);
    let sxi1 = params.xi1.mul(s);
    let pi = gqtau.add(sxi1);

    // compute pi
    // compute delta
    let mut delta = gen1.mul(r);
    delta = delta.sub(params.powers_of_tau[1].mul(s));
    delta = delta.add(gen1.mul(s.mul(u)));
    KZGProof { pi: pi.into(), delta: delta.into() }
}

pub fn verifyEval(C: G1Affine, v: Fr, u: Fr, proof: KZGProof, params: KZGParams) -> bool {
    // pleft
    let gen1 = G1::generator();
    let gen2 = G2::generator();
    let vgen1 = G1Affine::from(gen1).mul(v);
    let mut csvgen1 = C;
    csvgen1 = csvgen1.sub(G1Affine::from(vgen1)).into();
    let g2 = G2Affine::from(gen2);
    let pleft = Bn256::pairing(&csvgen1, &(g2));
    // pright1
    let ug2 = g2.mul(u);
    let tau2mug2 = params.tau2.sub(ug2);
    let pright1 = Bn256::pairing(&proof.pi, &G2Affine::from(tau2mug2));

    // pright2
    let pright2 = Bn256::pairing(&proof.delta, &params.xi2);
    // pleft =? pright1 - pright2
    let r1pr2 = pright1.add(pright2);
    pleft.eq(&r1pr2)
}

#[test]
fn test_kzg(){
    let params = setup(3);
    let p = [Fr::from(0), Fr::from(0), Fr::from(1)];
    let (C, r) = commit(&p, params.clone());
    let v = Fr::from(1);
    let u = Fr::from(1);
    let proof = proveEval(&[Fr::from(0), Fr::from(0), Fr::from(1)], v, u, r, params.clone());
    let b = verifyEval(G1Affine::from(C), v, u, proof.clone(), params.clone());
    assert!(b);
}
