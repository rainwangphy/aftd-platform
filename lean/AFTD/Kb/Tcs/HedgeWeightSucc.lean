import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.CumLossSucc
import AFTD.Kb.Tcs.HedgeWeight

/-!
# hedgeWeight_succ

Topic: learning   Node: 598d7008b806

Provenance: helper lemma. TCSlib, `hedgeWeight_succ`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Recursion for the Hedge weight. Fix a learning rate $\eta \in \bbr$ and a loss sequence $\ell$ for $N$ experts over $T$
rounds. For every round $t \in \mathrm{Fin}\,T$ and every expert $i \in
\mathrm{Fin}\,N$, the unnormalized Hedge weights satisfy
\[
  w_{t+1}(i) \;=\; w_t(i)\cdot \exp\!\bigl(-\eta\,\ell_t(i)\bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The weight update is multiplicative: `w_{t+1}(i) = w_t(i) · exp(-η · ℓ_t(i))` [FS97, §2]. -/
lemma hedgeWeight_succ {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : Fin T) (i : Fin N) :
    hedgeWeight η ℓ (t.val + 1) i = hedgeWeight η ℓ t.val i * Real.exp (-η * ℓ t i) := by
  simp only [hedgeWeight, cumLoss_succ]
  ring_nf
  rw [← exp_add]
  ring_nf
