import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLine
import AFTD.Kb.GameTheoryEconomics.IsStraightLineCutConsistent

/-!
# is_straight_line_cut_consistent_of_parallel_cuts

Topic: fair_division   Node: bd909d926db9

Provenance: helper lemma. arXiv:2610.27956 Section 4 (Splitting Planar Necklaces with Few Straight Cuts)

Let P be a finite set of points in ℝ × ℝ, φ a non-zero linear functional from ℝ × ℝ to ℝ, t₁ and t₂ real numbers with t₁ < t₂, and α an allocation function from ℝ × ℝ to Fin 3. If for every point p in P, α p = 0 implies φ p ≤ t₁, α p = 1 implies t₁ ≤ φ p and φ p ≤ t₂, and α p = 2 implies t₂ ≤ φ p, then there exists a finite set L of at most 2 straight lines such that α is consistent with L on P.
-/

open Classical

def is_straight_line_cut_consistent_of_parallel_cuts_cut_line
    (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (t : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
  φ.toAffineMap - AffineMap.const ℝ (ℝ × ℝ) t

theorem is_straight_line_cut_consistent_of_parallel_cuts_cut_line_linear
    (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (t : ℝ) :
    (is_straight_line_cut_consistent_of_parallel_cuts_cut_line φ t).linear = φ := by
  simp [is_straight_line_cut_consistent_of_parallel_cuts_cut_line]

def is_straight_line_cut_consistent_of_parallel_cuts_make_line
    (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (t : ℝ) : StraightLine :=
  ⟨is_straight_line_cut_consistent_of_parallel_cuts_cut_line φ t, by
    rw [is_straight_line_cut_consistent_of_parallel_cuts_cut_line_linear]; exact hφ⟩

theorem is_straight_line_cut_consistent_of_parallel_cuts_make_line_cut
    (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (t : ℝ) (p : ℝ × ℝ) :
    (is_straight_line_cut_consistent_of_parallel_cuts_make_line φ hφ t).cut p = φ p - t := rfl

theorem is_straight_line_cut_consistent_of_parallel_cuts_make_line_ne
    (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) {t₁ t₂ : ℝ} (ht : t₁ < t₂) :
    is_straight_line_cut_consistent_of_parallel_cuts_make_line φ hφ t₁ ≠
    is_straight_line_cut_consistent_of_parallel_cuts_make_line φ hφ t₂ := by
  intro h
  have h_cut : (is_straight_line_cut_consistent_of_parallel_cuts_make_line φ hφ t₁).cut 0 =
               (is_straight_line_cut_consistent_of_parallel_cuts_make_line φ hφ t₂).cut 0 := by rw [h]
  rw [is_straight_line_cut_consistent_of_parallel_cuts_make_line_cut,
      is_straight_line_cut_consistent_of_parallel_cuts_make_line_cut] at h_cut
  have hz : φ 0 = 0 := map_zero φ
  rw [hz] at h_cut
  linarith

noncomputable def is_straight_line_cut_consistent_of_parallel_cuts_s
    (ℓ₁ ℓ₂ : StraightLine) (α : (ℝ × ℝ) → Fin 3) :
    StraightLine → (ℝ × ℝ) → Bool :=
  fun ℓ p =>
    if ℓ = ℓ₁ then decide (α p ≠ 0)
    else if ℓ = ℓ₂ then decide (α p = 2)
    else false

theorem is_straight_line_cut_consistent_of_parallel_cuts_s_one
    (ℓ₁ ℓ₂ : StraightLine) (α : (ℝ × ℝ) → Fin 3) (p : ℝ × ℝ) :
    is_straight_line_cut_consistent_of_parallel_cuts_s ℓ₁ ℓ₂ α ℓ₁ p = decide (α p ≠ 0) := by
  dsimp [is_straight_line_cut_consistent_of_parallel_cuts_s]
  rw [if_pos rfl]

theorem is_straight_line_cut_consistent_of_parallel_cuts_s_two
    {ℓ₁ ℓ₂ : StraightLine} (hne : ℓ₂ ≠ ℓ₁) (α : (ℝ × ℝ) → Fin 3) (p : ℝ × ℝ) :
    is_straight_line_cut_consistent_of_parallel_cuts_s ℓ₁ ℓ₂ α ℓ₂ p = decide (α p = 2) := by
  dsimp [is_straight_line_cut_consistent_of_parallel_cuts_s]
  rw [if_neg hne, if_pos rfl]

lemma is_straight_line_cut_consistent_of_parallel_cuts_fin3_cases (x : Fin 3) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  revert x; decide

lemma is_straight_line_cut_consistent_of_parallel_cuts_fin3_eq {a b : Fin 3}
    (h1 : decide (a ≠ 0) = decide (b ≠ 0))
    (h2 : decide (a = 2) = decide (b = 2)) : a = b := by
  revert a b
  decide

/-- Consistency with two parallel cuts at distinct thresholds implies consistency with at most two straight lines. -/
theorem is_straight_line_cut_consistent_of_parallel_cuts
    (P : Finset (ℝ × ℝ)) (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (t₁ t₂ : ℝ)
    (α : (ℝ × ℝ) → Fin 3)
    (ht : t₁ < t₂)
    (hα : ∀ p ∈ P, (α p = 0 → φ p ≤ t₁) ∧ (α p = 1 → t₁ ≤ φ p ∧ φ p ≤ t₂) ∧ (α p = 2 → t₂ ≤ φ p)) :
    ∃ (L : Finset StraightLine), L.card ≤ 2 ∧ is_straight_line_cut_consistent P L α := by
  let ℓ₁ := is_straight_line_cut_consistent_of_parallel_cuts_make_line φ hφ t₁
  let ℓ₂ := is_straight_line_cut_consistent_of_parallel_cuts_make_line φ hφ t₂
  have hne : ℓ₂ ≠ ℓ₁ := by
    intro h
    exact (is_straight_line_cut_consistent_of_parallel_cuts_make_line_ne φ hφ ht) h.symm
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
