import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLine
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistent
import AFTD.Kb.GameTheoryEconomics.PlanarNecklaceTwoParallelCutsSixPoints
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistentOfParallelCuts
import AFTD.Kb.GameTheoryEconomics.IsParallelTwoCutConsistent

/-!
# planar_necklace_two_cuts_six_points

Topic: fair_division   Node: 9f1a02ac3e19

Provenance: formalization of a published result. Source: arXiv:2610.27956 Theorem 10 (Splitting Planar Necklaces with Few Straight Cuts)

For any finite set P of 6 points in the plane ℝ × ℝ colored with two colors c : (ℝ × ℝ) → Fin 2 such that exactly 3 points are colored 0 and 3 points are colored 1, there exists a finite set L of at most 2 straight lines and an allocation function α : (ℝ × ℝ) → Fin 3 consistent with L on P such that each of the three agents receives exactly 1 point of color 0 and 1 point of color 1.
-/

lemma planar_necklace_two_cuts_six_points_scale_linear_ne_zero (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) : (2 : ℝ) • φ ≠ 0 := by
  intro h
  apply hφ
  have : ((1/2 : ℝ) * (2 : ℝ)) • φ = (0 : (ℝ × ℝ) →ₗ[ℝ] ℝ) := by
    rw [mul_smul, h, smul_zero]
  norm_num at this
  exact this

lemma planar_necklace_two_cuts_six_points_scale_linear_ne (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) : (2 : ℝ) • φ ≠ φ := by
  intro h
  apply hφ
  have : ((2 : ℝ) - 1) • φ = (0 : (ℝ × ℝ) →ₗ[ℝ] ℝ) := by
    rw [sub_smul, one_smul, sub_eq_zero, h]
  norm_num at this
  exact this

lemma planar_necklace_two_cuts_six_points_make_line_scale_ne (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (s : ℝ) :
    is_straight_line_cut_consistent_of_parallel_cuts_make_line φ hφ s ≠
    is_straight_line_cut_consistent_of_parallel_cuts_make_line ((2:ℝ) • φ)
      (planar_necklace_two_cuts_six_points_scale_linear_ne_zero φ hφ) (2 * s) := by
  intro h
  have hlin : (is_straight_line_cut_consistent_of_parallel_cuts_make_line φ hφ s).cut.linear =
              (is_straight_line_cut_consistent_of_parallel_cuts_make_line ((2:ℝ) • φ)
                (planar_necklace_two_cuts_six_points_scale_linear_ne_zero φ hφ) (2 * s)).cut.linear := by
    rw [h]
  dsimp [is_straight_line_cut_consistent_of_parallel_cuts_make_line,
         is_straight_line_cut_consistent_of_parallel_cuts_cut_line] at hlin
  change φ.toAffineMap.linear - 0 = ((2:ℝ) • φ).toAffineMap.linear - 0 at hlin
  simp only [LinearMap.toAffineMap_linear, sub_zero] at hlin
  exact (planar_necklace_two_cuts_six_points_scale_linear_ne φ hφ) hlin.symm

lemma planar_necklace_two_cuts_six_points_of_parallel_cuts_eq
    (P : Finset (ℝ × ℝ)) (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (s : ℝ)
    (α : (ℝ × ℝ) → Fin 3)
    (hα : ∀ p ∈ P, (α p = 0 → φ p ≤ s) ∧ (α p = 1 → s ≤ φ p ∧ φ p ≤ s) ∧ (α p = 2 → s ≤ φ p)) :
    ∃ (L : Finset StraightLine), L.card ≤ 2 ∧ is_straight_line_cut_consistent P L α := by
  classical
  let ℓ₁ := is_straight_line_cut_consistent_of_parallel_cuts_make_line φ hφ s
  let ℓ₂ := is_straight_line_cut_consistent_of_parallel_cuts_make_line ((2:ℝ) • φ)
    (planar_necklace_two_cuts_six_points_scale_linear_ne_zero φ hφ) (2 * s)
  have hne : ℓ₂ ≠ ℓ₁ := (planar_necklace_two_cuts_six_points_make_line_scale_ne φ hφ s).symm
  use {ℓ₁, ℓ₂}
  refine ⟨Finset.card_le_two, ?_⟩
  dsimp [is_straight_line_cut_consistent]
  use is_straight_line_cut_consistent_of_parallel_cuts_s ℓ₁ ℓ₂ α
  refine ⟨?_, ?_⟩
  · intro ℓ hℓ p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
    rcases hα p hp with ⟨h0, h1, h2⟩
    rcases hℓ with rfl | rfl
    · rw [is_straight_line_cut_consistent_of_parallel_cuts_s_one,
          is_straight_line_cut_consistent_of_parallel_cuts_make_line_cut]
      constructor
      · intro hpos
        apply decide_eq_true
        intro ha0
        have := h0 ha0
        linarith
      · intro hneg
        apply decide_eq_false
        intro ha
        rcases is_straight_line_cut_consistent_of_parallel_cuts_fin3_cases (α p) with ha0 | ha1 | ha2
        · contradiction
        · have := (h1 ha1).1
          linarith
        · have := h2 ha2
          linarith
    · rw [is_straight_line_cut_consistent_of_parallel_cuts_s_two hne,
          is_straight_line_cut_consistent_of_parallel_cuts_make_line_cut]
      have hcut2 : ((2 : ℝ) • φ) p - 2 * s = 2 * (φ p - s) := by
        simp only [LinearMap.smul_apply, smul_eq_mul]
        ring
      rw [hcut2]
      constructor
      · intro hpos
        apply decide_eq_true
        rcases is_straight_line_cut_consistent_of_parallel_cuts_fin3_cases (α p) with ha0 | ha1 | ha2
        · have := h0 ha0
          linarith
        · have := (h1 ha1).2
          linarith
        · exact ha2
      · intro hneg
        apply decide_eq_false
        intro ha2
        have := h2 ha2
        linarith
  · intro p hp q hq hsame
    have hs1 : is_straight_line_cut_consistent_of_parallel_cuts_s ℓ₁ ℓ₂ α ℓ₁ p =
               is_straight_line_cut_consistent_of_parallel_cuts_s ℓ₁ ℓ₂ α ℓ₁ q :=
      hsame ℓ₁ (by simp)
    have hs2 : is_straight_line_cut_consistent_of_parallel_cuts_s ℓ₁ ℓ₂ α ℓ₂ p =
               is_straight_line_cut_consistent_of_parallel_cuts_s ℓ₁ ℓ₂ α ℓ₂ q :=
      hsame ℓ₂ (by simp)
    rw [is_straight_line_cut_consistent_of_parallel_cuts_s_one,
        is_straight_line_cut_consistent_of_parallel_cuts_s_one] at hs1
    rw [is_straight_line_cut_consistent_of_parallel_cuts_s_two hne,
        is_straight_line_cut_consistent_of_parallel_cuts_s_two hne] at hs2
    exact is_straight_line_cut_consistent_of_parallel_cuts_fin3_eq hs1 hs2

lemma planar_necklace_two_cuts_six_points_of_parallel_cuts_le
    (P : Finset (ℝ × ℝ)) (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (t₁ t₂ : ℝ)
    (α : (ℝ × ℝ) → Fin 3)
    (ht : t₁ ≤ t₂)
    (hα : ∀ p ∈ P, (α p = 0 → φ p ≤ t₁) ∧ (α p = 1 → t₁ ≤ φ p ∧ φ p ≤ t₂) ∧ (α p = 2 → t₂ ≤ φ p)) :
    ∃ (L : Finset StraightLine), L.card ≤ 2 ∧ is_straight_line_cut_consistent P L α := by
  rcases ht.lt_or_eq with hlt | heq
  · exact is_straight_line_cut_consistent_of_parallel_cuts P φ hφ t₁ t₂ α hlt hα
  · subst heq
    exact planar_necklace_two_cuts_six_points_of_parallel_cuts_eq P φ hφ t₁ α hα

/-- Theorem 10 of arXiv:2610.27956: two straight lines suffice to fairly allocate six points (three red and three blue) among three agents. -/
theorem planar_necklace_two_cuts_six_points
    (P : Finset (ℝ × ℝ)) (c : (ℝ × ℝ) → Fin 2)
    (hP_card : P.card = 6)
    (h_red : (P.filter (fun p => c p = 0)).card = 3)
    (h_blue : (P.filter (fun p => c p = 1)).card = 3) :
    ∃ (L : Finset StraightLine) (α : (ℝ × ℝ) → Fin 3),
      L.card ≤ 2 ∧
      is_straight_line_cut_consistent P L α ∧
      ∀ i : Fin 3,
        (P.filter (fun p => α p = i ∧ c p = 0)).card = 1 ∧
        (P.filter (fun p => α p = i ∧ c p = 1)).card = 1 := by
  obtain ⟨φ, t₁, t₂, α, hφ, h_cons, h_fair⟩ :=
    planar_necklace_two_parallel_cuts_six_points P c hP_card h_red h_blue
  rcases h_cons with ⟨ht, hα⟩
  obtain ⟨L, hL_card, hL_cons⟩ :=
    planar_necklace_two_cuts_six_points_of_parallel_cuts_le P φ hφ t₁ t₂ α ht hα
  exact ⟨L, α, hL_card, hL_cons, h_fair⟩
