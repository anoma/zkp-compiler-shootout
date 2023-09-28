use camino::Utf8Path;
use pasta_curves::{pallas, Fq};
use std::{cell::OnceCell, sync::Arc};

use lurk::{
    eval::{
        empty_sym_env,
        lang::{Coproc, Lang},
    },
    proof::nova::{NovaProver, PublicParams},
    proof::{nova::Proof, Prover},
    ptr::GPtr,
    public_parameters::public_params,
    store::Store,
    tag::ExprTag,
};
use tempfile::tempdir;

const FIB_PROGRAM: &str = r#"
(letrec ((next (lambda (a b) (next b (+ a b))))
           (fib (next 0 1)))
  (fib))
"#;

#[derive(Clone)]
pub struct Lurk {
    pub reduction_count: usize,
    pub input: usize,
    pub name: String,
}

impl<'a> zero_knowledge::ZeroKnowledge for Lurk {
    type C = (
        Option<Store<Fq>>,
        GPtr<Fq, ExprTag>,
        NovaProver<Fq, Coproc<Fq>>,
        Arc<Lang<pallas::Scalar, Coproc<pallas::Scalar>>>,
        Arc<PublicParams<'static, Fq, Coproc<Fq>>>,
    );
    type R = ReceiptWrapper;

    fn name(&self) -> String {
        self.name.clone()
    }

    fn compile(&self) -> Self::C {
        let mut store = Store::default();
        let lang_pallas = Lang::new();
        let lang_rc = Arc::new(lang_pallas.clone());

        let ptr: GPtr<Fq, _> = store.read(FIB_PROGRAM).unwrap();
        let prover = NovaProver::new(self.reduction_count, lang_pallas);

        // use cached public params
        // TODO re-use params across same reduction count. Also look into if IO can just be avoided.
        // Create a new temporary directory.
        let tmp_dir = tempdir().expect("Failed to create temporary directory");

        // Get the std::path::Path of the temporary directory and convert it to a Utf8Path.
        let std_path = tmp_dir.path();
        let utf8_path = Utf8Path::from_path(std_path)
            .expect("Failed to convert to Utf8Path")
            .to_owned();
        let pp = public_params(
            self.reduction_count,
            true,
            lang_rc.clone(),
            &utf8_path,
        )
        .unwrap();

        (Some(store), ptr, prover, lang_rc, pp)
    }

    fn prove(&self, (store, ptr, prover, lang_rc, pp): &mut Self::C) -> Self::R {
        let mut store = store.take().unwrap();
        let limit = fib_limit(self.input, self.reduction_count);

        let frames = prover
            .get_evaluation_frames(
                *ptr,
                empty_sym_env(&store),
                &mut store,
                limit,
                lang_rc.clone(),
            )
            .unwrap();

        let receipt_wrapper = ReceiptWrapper {
            receipt: OnceCell::new(),
            store,
        };

        receipt_wrapper.receipt.get_or_init(|| {
            let (proof, z0, zi, num_steps) = prover
                .prove(&pp, &frames, &receipt_wrapper.store, lang_rc.clone())
                .unwrap();
            // SAFETY: a static lifetime transmute is required without refactoring the benchmarking framework
            //         since lurk proofs include a lifetime to the state object. This is safe in
            //         this context since the store is dropped after the receipt.
            (unsafe { std::mem::transmute(proof) }, z0, zi, num_steps)
        });

        receipt_wrapper
    }

    fn verify(&self, receipt_wrapper: Self::R, (_, _, _, _, pp): &mut Self::C) {
        let (proof, z0, zi, num_steps) = receipt_wrapper.receipt.get().unwrap();
        proof.verify(&pp, *num_steps, &z0, &zi).unwrap();
    }
}

/// Wrapper for the Lurk receipt to get around the proof store lifetime being tied to the proof
/// that needs to be passed on through to the verify step without a lifetime.
///
/// This handles it by just having a self-referential struct with a static lifetime. Should not
/// use any fields manually, and the receipt will be dropped before store.
pub struct ReceiptWrapper {
    receipt: OnceCell<(Proof<'static, Fq, Coproc<Fq>>, Vec<Fq>, Vec<Fq>, usize)>,

    store: Store<Fq>,
}

impl Drop for ReceiptWrapper {
    fn drop(&mut self) {
        // SAFETY: Be sure that the proof is dropped first, in case there are some semantics
        //         in the future that interact with the store on drop.
        drop(self.receipt.take());
    }
}

// The env output in the `fib_frame`th frame of the above, infinite Fibonacci computation will contain a binding of the
// nth Fibonacci number to `a`.
fn fib_frame(n: usize) -> usize {
    11 + 16 * n
}

// Set the limit so the last step will be filled exactly, since Lurk currently only pads terminal/error continuations.
fn fib_limit(n: usize, rc: usize) -> usize {
    let frame = fib_frame(n);
    rc * (frame / rc + usize::from(frame % rc != 0))
}
