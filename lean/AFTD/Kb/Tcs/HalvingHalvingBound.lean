import AFTD.Prelude
import AFTD.Kb.Tcs.HalvingMistakesBound
import AFTD.Kb.Tcs.HalvingMistakes

/-!
# Halving.halving_bound

Topic: learning   Node: d9f1f1ed25a9

Provenance: formalization of a published result. Source: Halving mistake bound, as formalized in TCSlib (`Halving.halving_bound`). Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/MistakeBounds/Halving.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Halving mistake bound. Let $\mathtt{eval} : \mathit{Hyp} \to X \to \mathsf{Bool}$ assign a Boolean label to
each input under each hypothesis, let $H$ be a finite class of hypotheses, and fix a
target hypothesis $\mathtt{target} \in H$ that supplies the correct label
$\mathtt{eval}(\mathtt{target}, x)$ for every input $x$. Then, on any finite sequence
$xs$ of inputs, the number of mistakes made by the Halving Algorithm run from the
initial version space $H$ is at most $\lfloor \log_2 \abs{H} \rfloor$:
\[
\mathtt{mistakes}(\mathtt{eval}, \mathtt{target}, H, xs) \;\le\; \lfloor \log_2 \abs{H}
\rfloor.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {Hyp X : Type*} in
/-- The Halving mistake bound from the initial finite hypothesis class `H`: in the realizable setting (`target ∈ H`), the Halving Algorithm makes at most `⌊log₂ |H|⌋` mistakes on any finite list of inputs labelled by `target`. This is `mistakes_bound` with `V := H`. [MRT18, Thm 8.1]; origin [Lit88, §3]. Deviation: `Nat.log 2 H.card` (floor of `log₂ |H|`) over an explicit finite example list with an explicit realizable target, versus the source's `opt(H) ≤ log₂ |H|` for the adversarial online model. -/
theorem Halving.halving_bound
    (eval : Hyp → X → Bool) (target : Hyp) (H : Finset Hyp) (xs : List X)
    (htarget : target ∈ H) :
    mistakes eval target H xs ≤ Nat.log 2 H.card :=
  mistakes_bound eval target H xs htarget
