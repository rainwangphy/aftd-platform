import AFTD.Prelude
import AFTD.Kb.Tcs.HalvingVoteFor

/-!
# Halving.update

Topic: learning   Node: 93eb5ba0f1b8

Provenance: formalization of a published result. Source: TCSlib, `Halving.update`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/MistakeBounds/Halving.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

After observing that the correct label for input $x$ is $y$, the version space is
updated to $\mathtt{update}(\mathtt{eval}, V, x, y) = \mathtt{voteFor}(\mathtt{eval},
V, x, y)$, i.e.\ only the hypotheses that correctly predict $y$ on $x$ are retained.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {Hyp X : Type*} in
/-- The version space after observing the labelled example `(x, y)`: the hypotheses of `V` that agree with the label `y` on `x`; every hypothesis that voted for the other label is discarded. [MRT18, §8.2.1 (Halving algorithm)]; origin [Lit88, §3]. -/
def Halving.update (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) (y : Bool) :
    Finset Hyp :=
  voteFor eval V x y
