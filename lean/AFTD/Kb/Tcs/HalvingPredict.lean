import AFTD.Prelude
import AFTD.Kb.Tcs.HalvingVoteFor
import AFTD.Kb.Tcs.V

/-!
# Halving.predict

Topic: learning   Node: ea82776d2f39

Provenance: formalization of a published result. Source: TCSlib, `Halving.predict`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/MistakeBounds/Halving.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Halving Algorithm predicts on input $x$ by taking a majority vote of the current
version space $V$: it returns $\mathsf{true}$ whenever the number of hypotheses in $V$
that predict $\mathsf{true}$ is at least as large as the number that predict
$\mathsf{false}$ (ties are broken in favour of $\mathsf{true}$).
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {Hyp X : Type*} in
/-- The Halving prediction on the input `x`: the label that receives the majority of the votes of the version space `V`, with ties broken towards `true`. [MRT18, §8.2.1 (Halving algorithm)]; origin [Lit88, §3]. -/
def Halving.predict (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) : Bool :=
  if (voteFor eval V x true).card ≥ (voteFor eval V x false).card then
    true
  else
    false
