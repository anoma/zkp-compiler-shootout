// Standard Interface everyone will implement. to effectively
// benchmark
pub trait ZeroKnowledge {
    type C;
    type R;
    fn name(&self) -> String;
    fn compile(&self) -> Self::C;
    fn prove(&self, setup: &mut Self::C) -> Self::R;
    fn verify(&self, receipt: Self::R, program: &mut Self::C) -> ();
    fn prove_and_verify(&self) -> () {
        let mut circuit = self.compile();
        let receipt = self.prove(&mut circuit);
        self.verify(receipt, &mut circuit);
    }
}
