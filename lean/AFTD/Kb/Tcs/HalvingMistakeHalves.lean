import AFTD.Prelude
import AFTD.Kb.Tcs.HalvingPredict
import AFTD.Kb.Tcs.HalvingUpdate
import AFTD.Kb.Tcs.HalvingVoteFor
import AFTD.Kb.Tcs.HalvingVoteForFalseAddTrue
import AFTD.Kb.Tcs.V

/-!
# Halving.mistake_halves

Topic: learning   Node: 28463b43f9dd

Provenance: helper lemma. TCSlib, `Halving.mistake_halves`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/MistakeBounds/Halving.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Mistake bound for the Halving algorithm. Let $\mathtt{eval} : \mathit{Hyp} \to X \to \mathsf{Bool}$ be an evaluation map, let $V
\subseteq \mathit{Hyp}$ be a finite version space, let $x \in X$ be an input, and let $y
\in \mathsf{Bool}$ be its true label. If the Halving prediction on $x$ is wrong, that is
$\mathtt{predict}(\mathtt{eval}, V, x) \ne y$, then the updated version space contains
at most half of the hypotheses:
\[
  2 \cdot \abs{\mathtt{update}(\mathtt{eval}, V, x, y)} \le \abs{V}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {Hyp X : Type*} in
/-- Every mistake at least halves the version space: if the Halving prediction on `x` differs from the observed label `y`, then the version space updated on `(x, y)` has at most half as many hypotheses as `V`, i.e. `2 · |update eval V x y| ≤ |V|`. [MRT18, proof of Thm 8.1]. **Proof sketch.** Case on the label `y`. If the prediction was wrong, the majority (ties included) voted for the other label, so the voters for `y` are at most the voters against `y`. Since the two vote sets partition `V` (`voteFor_false_add_true`), the survivors number at most half of `V`. -/
lemma Halving.mistake_halves
    (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) (y : Bool)
    (hmistake : predict eval V x ≠ y) :
    2 * (update eval V x y).card ≤ V.card := by
  cases y
  · -- true label is false/0, so a mistake means the algorithm predicted true/1.
    unfold predict at hmistake
    by_cases hmaj :
        (voteFor eval V x true).card ≥ (voteFor eval V x false).card
    · have hsum := voteFor_false_add_true (eval := eval) (V := V) (x := x)
      simp [update, hmaj] at hmistake ⊢
      omega
    · simp [hmaj] at hmistake
  · -- true label is true/1, so a mistake means the algorithm predicted false/0.
    unfold predict at hmistake
    by_cases hmaj :
        (voteFor eval V x true).card ≥ (voteFor eval V x false).card
    · simp [hmaj] at hmistake
    · have hsum := voteFor_false_add_true (eval := eval) (V := V) (x := x)
      have hle :
          (voteFor eval V x true).card ≤
            (voteFor eval V x false).card := by
        omega
      simp [update, hmaj] at hmistake ⊢
      omega
