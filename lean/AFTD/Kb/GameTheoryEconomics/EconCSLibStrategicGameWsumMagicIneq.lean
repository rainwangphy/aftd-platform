import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.wsum_magic_ineq

Topic: equilibria   Node: 2a4e4aeba93b

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.wsum_magic_ineq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Helper: weighted-average inequality on the simplex. If `∑_i σ_i * f_i = c`, then there exists `i` with `0 < σ_i` and `f i ≤ c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Function in
set_option linter.unusedSectionVars false in
variable {N : Type*} in
variable (G : EconCSLib.StrategicGame N ℝ) in
variable [Fintype N] [DecidableEq N] in
variable [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)] in
variable [∀ i, Inhabited (G.strategy i)] in
/-- Helper: weighted-average inequality on the simplex. If `∑_i σ_i * f_i = c`, then there exists `i` with `0 < σ_i` and `f i ≤ c`. -/
lemma EconCSLib.StrategicGame.wsum_magic_ineq {X : Type*} [Fintype X]
    {p : stdSimplex ℝ X} {f : X → ℝ} {c : ℝ}
    (H : ∑ a : X, p.val a * f a = c) : ∃ a, 0 < p.val a ∧ f a ≤ c := by
  by_contra Hall
  push_neg at Hall
  -- Hall : ∀ a, 0 < p.val a → c < f a (after push_neg of ∀ a, ¬(0 < p.val a ∧ f a ≤ c))
  -- Actually push_neg gives: ∀ a, 0 < p.val a → c < f a
  have hpos : ∃ a, 0 < p.val a := by
    by_contra h_all_npos
    push_neg at h_all_npos
    have hzero : ∀ a, p.val a = 0 :=
      fun a => le_antisymm (h_all_npos a) (p.property.1 a)
    have : (∑ a : X, p.val a) = 0 := by simp [hzero]
    linarith [p.property.2]
  have hgt : c < ∑ a : X, p.val a * f a := by
    have hsum_c : ∑ a : X, p.val a * c = c := by
      rw [← Finset.sum_mul, p.property.2, one_mul]
    rw [← hsum_c]
    apply Finset.sum_lt_sum
    · intro a _
      by_cases ha : 0 < p.val a
      · exact mul_le_mul_of_nonneg_left (Hall a ha).le (p.property.1 a)
      · push_neg at ha
        have := le_antisymm ha (p.property.1 a)
        simp [this]
    · obtain ⟨a₀, ha₀⟩ := hpos
      exact ⟨a₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (Hall a₀ ha₀) ha₀⟩
  linarith [H ▸ hgt]
