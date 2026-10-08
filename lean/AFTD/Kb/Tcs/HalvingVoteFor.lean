import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# Halving.voteFor

Topic: learning   Node: f2f329915190

Provenance: formalization of a published result. Source: TCSlib, `Halving.voteFor`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/MistakeBounds/Halving.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given an evaluation map $\mathtt{eval} : \mathit{Hyp} \to X \to \mathsf{Bool}$, a
version space $V \subseteq \mathit{Hyp}$, an input $x \in X$, and a label
$y \in \mathsf{Bool}$, $\mathtt{voteFor}(\mathtt{eval}, V, x, y)$ is the subset of $V$
consisting of all hypotheses that predict label $y$ on input $x$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {Hyp X : Type*} in
/-- The set of hypotheses in the version space `V` whose evaluation on the input `x` equals the label `y`, i.e. the hypotheses that vote for `y` on `x`. [MRT18, §8.2.1 (Halving algorithm)]; origin [Lit88, §3]. -/
def Halving.voteFor (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) (y : Bool) :
    Finset Hyp :=
  V.filter (fun h => eval h x = y)
