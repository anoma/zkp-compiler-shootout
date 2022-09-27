// Standard Interface everyone will implement. to effectively
// benchmark
pub trait ZeroKnowledge {
    type C;
    type R;
    fn name(&self) -> String;
    fn compile(&self) -> Self::C;
    fn prove(&self, setup: &Self::C) -> Self::R;
    fn verify(&self, receipt: Self::R, program: &Self::C) -> ();
    fn prove_and_verify(&self) -> () {
        let circuit = self.compile();
        let receipt = self.prove(&circuit);
        self.verify(receipt, &circuit);
    }
}
