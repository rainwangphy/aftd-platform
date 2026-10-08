import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.Tcs.CumLoss

/-!
# cumLoss_succ

Topic: learning   Node: f36842bdd56d

Provenance: helper lemma. TCSlib, `cumLoss_succ`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Basic.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cumulative loss recurrence. Let $\ell$ be a loss sequence for $N$ experts over $T$ rounds, and write $L_t(i) =
\sum_{s < t} \ell_s(i)$ for the cumulative loss of expert $i$ through the first $t$
rounds. Then for every round $t < T$ and every expert $i$,
\[
  L_{t+1}(i) \;=\; L_t(i) + \ell_t(i).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The cumulative loss through `t + 1` rounds is the cumulative loss through `t` rounds plus the loss at round `t`: `L_{t+1}(i) = L_t(i) + ℓ_t(i)`. -/
lemma cumLoss_succ {N T : ℕ} (ℓ : LossSeq N T) (t : Fin T) (i : Fin N) :
    cumLoss ℓ (t.val + 1) i = cumLoss ℓ t.val i + ℓ t i := by
  simp only [cumLoss]
  -- The prefix `{s | s < t+1}` is the old prefix `{s | s < t}` plus the
  -- current round `t`.
  have : (Finset.univ (α := Fin T)).filter (fun s => s.val < t.val + 1) =
      ((Finset.univ).filter (fun s => s.val < t.val)) ∪ {t} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · intro h; by_cases hs : s = t
      · exact Or.inr hs
      · left; omega
    · rintro (h | rfl)
      · omega
      · omega
  rw [this, Finset.sum_union]
  · simp
  · simp [Finset.disjoint_left]
    intro s hs
    omega
