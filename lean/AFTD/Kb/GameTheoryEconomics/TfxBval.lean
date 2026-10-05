import AFTD.Prelude

/-!
# tfx_bval

Topic: fair_division   Node: 21cb965238fb

Temporal fair division under the identical-days setting (arXiv 2607.17224, arXiv 2601.12835): two agents, T rounds, and in every round one fresh copy of each of m good types arrives (so all rounds carry identical sets of goods). An allocation σ gives the copy of type g arriving in round s to agent σ s g. tfx_bval v σ t i j is agent i's (additive) value for the cumulative bundle of agent j after rounds 0, …, t.
-/

open Finset in
/-- Temporal fair division under the identical-days setting (arXiv 2607.17224, arXiv 2601.12835): two agents, `T` rounds, and in every round one fresh copy of each of `m` good types arrives (so all rounds carry identical sets of goods). An allocation `σ` gives the copy of type `g` arriving in round `s` to agent `σ s g`. `tfx_bval v σ t i j` is agent `i`'s (additive) value for the cumulative bundle of agent `j` after rounds `0, …, t`. -/
noncomputable def tfx_bval {T m : ℕ} (v : Fin 2 → Fin m → ℝ) (σ : Fin T → Fin m → Fin 2)
    (t : ℕ) (i j : Fin 2) : ℝ :=
  ∑ s : Fin T, ∑ g : Fin m, if s.val ≤ t ∧ σ s g = j then v i g else 0
