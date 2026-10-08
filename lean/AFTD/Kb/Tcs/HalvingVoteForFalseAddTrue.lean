import AFTD.Prelude
import AFTD.Kb.Tcs.HalvingVoteFor

/-!
# Halving.voteFor_false_add_true

Topic: learning   Node: 54ba44a80ec7

Provenance: helper lemma. TCSlib, `Halving.voteFor_false_add_true`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/MistakeBounds/Halving.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Vote counts partition the version space. Let $\mathrm{eval}$ be a Boolean evaluation map assigning to each hypothesis and each
input a truth value, let $V$ be a finite version space of hypotheses, and let $x$ be an
input. Every hypothesis in $V$ predicts either $\mathsf{false}$ or $\mathsf{true}$ on
$x$, so the number of hypotheses in $V$ predicting $\mathsf{false}$ on $x$ and the
number predicting $\mathsf{true}$ on $x$ sum to the total number of hypotheses in $V$:
\[
  \abs{\{\,h \in V : \mathrm{eval}(h, x) = \mathsf{false}\,\}} +
  \abs{\{\,h \in V : \mathrm{eval}(h, x) = \mathsf{true}\,\}} = \abs{V}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {Hyp X : Type*} in
/-- The number of hypotheses of `V` voting `false` on `x` plus the number voting `true` on `x` equals the size of `V`: the two vote sets partition the current version space. -/
lemma Halving.voteFor_false_add_true
    (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) :
    (voteFor eval V x false).card + (voteFor eval V x true).card = V.card := by
  unfold voteFor
  have hfilter :
      V.filter (fun h : Hyp => eval h x = true) =
        V.filter (fun h : Hyp => ¬ eval h x = false) := by
    ext h
    cases eval h x <;> simp
  rw [hfilter]
  exact Finset.card_filter_add_card_filter_not
    (s := V) (p := fun h : Hyp => eval h x = false)
