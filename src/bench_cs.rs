use std::marker::PhantomData;

use snarkos_models::{
    curves::{PairingEngine, PrimeField},
    gadgets::r1cs::{ConstraintSystem, Index, LinearCombination, Variable}
};
use snarkos_errors::gadgets::SynthesisError;

#[derive(Debug)]
pub struct BenchCS<F: PrimeField> {
    inputs: usize,
    aux: usize,
    a: usize,
    b: usize,
    c: usize,
    num_constraints: usize,
    _e: PhantomData<F>,
}

impl<F: PrimeField> BenchCS<F> {
    pub fn new() -> Self {
        BenchCS::default()
    }

    pub fn num_constraints(&self) -> usize {
        self.a
    }

    pub fn num_inputs(&self) -> usize {
        self.inputs
    }
}

impl<F: PrimeField> Default for BenchCS<F> {
    fn default() -> Self {
        BenchCS {
            inputs: 1,
            aux: 0,
            a: 0,
            b: 0,
            c: 0,
            num_constraints: 0,
            _e: PhantomData,
        }
    }
}

impl<F: PrimeField> ConstraintSystem<F> for BenchCS<F> {
    type Root = Self;

    fn alloc<FN, A, AR>(&mut self, _: A, _f: FN) -> Result<Variable, SynthesisError>
    where
        FN: FnOnce() -> Result<F, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // don't invoke f, we just count
        self.aux += 1;

        Ok(Variable::new_unchecked(Index::Aux(self.aux - 1)))
    }

    fn alloc_input<FN, A, AR>(&mut self, _: A, _f: FN) -> Result<Variable, SynthesisError>
    where
        FN: FnOnce() -> Result<F, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // don't invoke f, we just count
        self.inputs += 1;

        Ok(Variable::new_unchecked(Index::Input(self.inputs - 1)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, _a: LA, _b: LB, _c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<F>) -> LinearCombination<F>,
        LB: FnOnce(LinearCombination<F>) -> LinearCombination<F>,
        LC: FnOnce(LinearCombination<F>) -> LinearCombination<F>,
    {
        self.a += 1;
        self.b += 1;
        self.c += 1;
        self.num_constraints += 1;
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn pop_namespace(&mut self) {}

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }

    fn num_constraints(&self) -> usize {
        self.num_constraints
    }
}
