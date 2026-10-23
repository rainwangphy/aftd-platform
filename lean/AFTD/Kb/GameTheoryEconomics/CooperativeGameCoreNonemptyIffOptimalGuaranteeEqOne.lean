import AFTD.Prelude

/-!
# cooperative_game_core_nonempty_iff_optimal_guarantee_eq_one

Topic: general_equilibrium   Node: 52cd8970ca70

Provenance: helper lemma. scout/2610-29731-computing-the-nucleon-of-matching-games.md:1189

For a cooperative game v on a finite player set N with nonnegative values and positive grand coalition value v(N) > 0, an optimal multiplicative least-core guarantee r ∈ (0, 1] satisfies r = 1 if and only if the game has a nonempty core (there exists a nonnegative vector y summing to v(N) such that y(T) ≥ v(T) for all coalitions T ⊆ N).
-/

/-- A nonnegative cooperative game has an optimal multiplicative least-core guarantee of 1 iff its core is nonempty. -/
theorem cooperative_game_core_nonempty_iff_optimal_guarantee_eq_one
    {N : Type*} [DecidableEq N] [Fintype N]
    (v : Finset N → ℝ) (r : ℝ)
    (h_nonneg : ∀ S, 0 ≤ v S) (hW : 0 < v Finset.univ)
    (hr_bounds : 0 < r ∧ r ≤ 1)
    (hr : (∃ y : N → ℝ, (∀ i, 0 ≤ y i) ∧ Finset.univ.sum y = v Finset.univ ∧
            ∀ T : Finset N, 0 < v T → r * v T ≤ T.sum y) ∧
          (∀ y : N → ℝ, (∀ i, 0 ≤ y i) → Finset.univ.sum y = v Finset.univ →
            ∃ T : Finset N, 0 < v T ∧ T.sum y ≤ r * v T)) :
    (r = 1 ↔ ∃ y : N → ℝ, (∀ i, 0 ≤ y i) ∧ Finset.univ.sum y = v Finset.univ ∧
      ∀ T : Finset N, v T ≤ T.sum y) := by
  have _ := hW
  constructor
  · rintro rfl
    obtain ⟨y, hy_nonneg, hy_sum, hy_core⟩ := hr.1
    refine ⟨y, hy_nonneg, hy_sum, fun T => ?_⟩
    by_cases hT : 0 < v T
    · have := hy_core T hT
      simpa using this
    · have h0 : v T = 0 := le_antisymm (not_lt.mp hT) (h_nonneg T)
      rw [h0]
      exact Finset.sum_nonneg (fun i _ => hy_nonneg i)
  · rintro ⟨y, hy_nonneg, hy_sum, hy_core⟩
    obtain ⟨T, hT_pos, hT_le⟩ := hr.2 y hy_nonneg hy_sum
    have h1 : v T ≤ T.sum y := hy_core T
    have h2 : v T ≤ r * v T := le_trans h1 hT_le
    have hr_ge_one : 1 ≤ r := by nlinarith
    exact le_antisymm hr_bounds.2 hr_ge_one
