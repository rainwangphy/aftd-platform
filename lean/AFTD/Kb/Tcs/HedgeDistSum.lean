import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.HedgeDist
import AFTD.Kb.Tcs.PotentialPos

/-!
# hedgeDist_sum

Topic: learning   Node: f4cc39f1f729

Provenance: helper lemma. TCSlib, `hedgeDist_sum`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Hedge distribution sums to one. Fix a number of experts $N \ge 1$, a horizon $T$, a learning rate $\eta \in \bbr$, a
loss sequence $\ell$ for $N$ experts over $T$ rounds, and a round $t$. Then the Hedge
distribution at round $t$ sums to one over all experts,
\[
  \sum_{i=1}^{N} p_t(i) = 1,
\]
so it is a probability distribution on the $N$ experts.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The Hedge distribution at any round is a probability vector: its coordinates sum to `1`. -/
lemma hedgeDist_sum {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) :
    ∑ i : Fin N, hedgeDist η ℓ t i = 1 := by
  -- Normalization by the positive potential turns weights into a probability
  -- distribution.
  simp only [hedgeDist]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (potential_pos η ℓ t))
