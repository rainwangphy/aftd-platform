import AFTD.Prelude
import AFTD.Kb.Tcs.OptimalTorusError
import AFTD.Kb.Tcs.PredictedTorusError
import AFTD.Kb.Tcs.HasRationalTorusApproximation
import AFTD.Kb.Tcs.BoolAnfCoefficient
import AFTD.Kb.Tcs.HasTorusApproximation
import AFTD.Kb.Tcs.BoolNextToTopAnfCount
import AFTD.Kb.Tcs.DegreeSpace
import AFTD.Kb.Tcs.Bit

/-!
# op_729_case_n_two

Topic: circuits   Node: 5c8992ef669c

Provenance: helper lemma. arXiv:2610.19174, Majority and Torus Polynomials: Bounded-Lift Lower Bounds and Explicit Constructions

For every Boolean function f : (Fin 2 → Bool) → Bool on 2 variables, optimalTorusError f 0 = predictedTorusError 2 f and HasRationalTorusApproximation f 0 (predictedTorusError 2 f).
-/

private theorem op_729_case_n_two_predicted_two (f : (Fin 2 → Bool) → Bool) :
    predictedTorusError 2 f = if boolAnfCoefficient f Finset.univ = false ∧ boolNextToTopAnfCount f = 0 then 0 else 1 / 4 := by
  dsimp [predictedTorusError]
  by_cases h1 : boolAnfCoefficient f Finset.univ = true
  · rw [if_pos h1]
    have hnot : ¬ (boolAnfCoefficient f Finset.univ = false ∧ boolNextToTopAnfCount f = 0) := by
      rintro ⟨h, _⟩; rw [h1] at h; contradiction
    rw [if_neg hnot]
    norm_num
  · rw [if_neg h1]
    have h1' : boolAnfCoefficient f Finset.univ = false := Bool.eq_false_iff.mpr h1
    by_cases h2 : boolNextToTopAnfCount f = 0
    · rw [if_pos h2, if_pos ⟨h1', h2⟩]
    · rw [if_neg h2]
      have hnot : ¬ (boolAnfCoefficient f Finset.univ = false ∧ boolNextToTopAnfCount f = 0) := by
        rintro ⟨_, hk0⟩; exact h2 hk0
      rw [if_neg hnot]
      have hk_le : boolNextToTopAnfCount f ≤ 2 := by
        unfold boolNextToTopAnfCount
        have : (Finset.univ : Finset (Fin 2)).card = 2 := by rfl
        exact le_trans (Finset.card_filter_le _ _) (le_of_eq this)
      have hk_cases : boolNextToTopAnfCount f = 1 ∨ boolNextToTopAnfCount f = 2 := by
        omega
      rcases hk_cases with hk1 | hk2
      · rw [hk1]; norm_num
      · rw [hk2]; norm_num

private theorem op_729_case_n_two_anf_cond_iff_const (f : (Fin 2 → Bool) → Bool) :
    (boolAnfCoefficient f Finset.univ = false ∧ boolNextToTopAnfCount f = 0) ↔
    (∀ x, f x = false) ∨ (∀ x, f x = true) := by
  revert f
  decide

private theorem op_729_case_n_two_hasRat_quarter (f : (Fin 2 → Bool) → Bool) :
    HasRationalTorusApproximation f 0 (1 / 4) := by
  use (fun _ => (1 / 4 : ℚ))
  refine ⟨?_, ?_⟩
  · have hempty : (fun (_ : Fin 2 → Bool) => (1 : ℚ)) ∈ degreeSpace ℚ (Fin 2) 0 := by
      apply Submodule.subset_span
      use ∅
      refine ⟨by simp, ?_⟩
      ext x; simp
    have : (fun (_ : Fin 2 → Bool) => (1 / 4 : ℚ)) = (1 / 4 : ℚ) • (fun (_ : Fin 2 → Bool) => (1 : ℚ)) := by
      ext x; simp
    rw [this]
    exact Submodule.smul_mem _ _ hempty
  · use (fun _ => (0 : ℤ))
    intro x
    cases f x <;> norm_num [bit]

private theorem op_729_case_n_two_hasRat_zero_of_false (f : (Fin 2 → Bool) → Bool) (hf : ∀ x, f x = false) :
    HasRationalTorusApproximation f 0 0 := by
  use (fun _ => (0 : ℚ))
  refine ⟨Submodule.zero_mem _, ?_⟩
  use (fun _ => (0 : ℤ))
  intro x
  simp [bit, hf x]

private theorem op_729_case_n_two_hasRat_zero_of_true (f : (Fin 2 → Bool) → Bool) (hf : ∀ x, f x = true) :
    HasRationalTorusApproximation f 0 0 := by
  use (fun _ => (1 / 2 : ℚ))
  refine ⟨?_, ?_⟩
  · have hempty : (fun (_ : Fin 2 → Bool) => (1 : ℚ)) ∈ degreeSpace ℚ (Fin 2) 0 := by
      apply Submodule.subset_span
      use ∅
      refine ⟨by simp, ?_⟩
      ext x; simp
    have : (fun (_ : Fin 2 → Bool) => (1 / 2 : ℚ)) = (1 / 2 : ℚ) • (fun (_ : Fin 2 → Bool) => (1 : ℚ)) := by
      ext x; simp
    rw [this]
    exact Submodule.smul_mem _ _ hempty
  · use (fun _ => (0 : ℤ))
    intro x
    simp [bit, hf x]

private theorem op_729_case_n_two_hasTorus_zero_of_false (f : (Fin 2 → Bool) → Bool) (hf : ∀ x, f x = false) :
    HasTorusApproximation f 0 0 := by
  use (fun _ => (0 : ℝ))
  refine ⟨Submodule.zero_mem _, (fun _ => (0 : ℤ)), ?_⟩
  intro x
  simp [bit, hf x]

private theorem op_729_case_n_two_hasTorus_zero_of_true (f : (Fin 2 → Bool) → Bool) (hf : ∀ x, f x = true) :
    HasTorusApproximation f 0 0 := by
  use (fun _ => (1 / 2 : ℝ))
  refine ⟨?_, (fun _ => (0 : ℤ)), ?_⟩
  · have hempty : (fun (_ : Fin 2 → Bool) => (1 : ℝ)) ∈ degreeSpace ℝ (Fin 2) 0 := by
      apply Submodule.subset_span
      use ∅
      refine ⟨by simp, ?_⟩
      ext x; simp
    have : (fun (_ : Fin 2 → Bool) => (1 / 2 : ℝ)) = (1 / 2 : ℝ) • (fun (_ : Fin 2 → Bool) => (1 : ℝ)) := by
      ext x; simp
    rw [this]
    exact Submodule.smul_mem _ _ hempty
  · intro x
    simp [bit, hf x]

private theorem op_729_case_n_two_hasTorus_quarter (f : (Fin 2 → Bool) → Bool) :
    HasTorusApproximation f 0 (1 / 4) := by
  use (fun _ => (1 / 4 : ℝ))
  refine ⟨?_, ?_⟩
  · have hempty : (fun (_ : Fin 2 → Bool) => (1 : ℝ)) ∈ degreeSpace ℝ (Fin 2) 0 := by
      apply Submodule.subset_span
      use ∅
      refine ⟨by simp, ?_⟩
      ext x; simp
    have : (fun (_ : Fin 2 → Bool) => (1 / 4 : ℝ)) = (1 / 4 : ℝ) • (fun (_ : Fin 2 → Bool) => (1 : ℝ)) := by
      ext x; simp
    rw [this]
    exact Submodule.smul_mem _ _ hempty
  · use (fun _ => (0 : ℤ))
    intro x
    cases f x <;> norm_num [bit]

private theorem op_729_case_n_two_opt_zero (f : (Fin 2 → Bool) → Bool)
    (h0 : HasTorusApproximation f 0 0) :
    optimalTorusError f 0 = 0 := by
  unfold optimalTorusError
  apply IsLeast.csInf_eq
  refine ⟨h0, ?_⟩
  intro ε hε
  rcases hε with ⟨P, _, Z, hZ⟩
  have : 0 ≤ |P (fun _ => false) - (Z (fun _ => false) : ℝ) - bit (f (fun _ => false)) / 2| := abs_nonneg _
  exact le_trans this (hZ (fun _ => false))

private theorem op_729_case_n_two_opt_ge_quarter (f : (Fin 2 → Bool) → Bool)
    (x0 x1 : Fin 2 → Bool) (hf0 : f x0 = false) (hf1 : f x1 = true)
    (ε : ℝ) (hε : HasTorusApproximation f 0 ε) :
    1 / 4 ≤ ε := by
  rcases hε with ⟨P, hP, Z, hZ⟩
  have hset : { g : (Fin 2 → Bool) → ℝ | ∃ S : Finset (Fin 2), S.card ≤ 0 ∧ g = fun x => ∏ i ∈ S, if x i then (1 : ℝ) else 0 }
      ⊆ { fun _ => (1 : ℝ) } := by
    intro g hg
    rcases hg with ⟨S, hS, rfl⟩
    have : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
    subst this
    simp
  have hspan := Submodule.span_mono hset hP
  rcases Submodule.mem_span_singleton.mp hspan with ⟨c, rfl⟩
  have h0 : |c • (fun _ => (1 : ℝ)) x0 - (Z x0 : ℝ) - bit (f x0) / 2| ≤ ε := hZ x0
  have h1 : |c • (fun _ => (1 : ℝ)) x1 - (Z x1 : ℝ) - bit (f x1) / 2| ≤ ε := hZ x1
  have hbit0 : bit (f x0) = 0 := by rw [hf0]; rfl
  have hbit1 : bit (f x1) = 1 := by rw [hf1]; rfl
  rw [hbit0] at h0
  rw [hbit1] at h1
  simp only [smul_eq_mul, mul_one] at h0 h1
  have h0' : |c - (Z x0 : ℝ)| ≤ ε := by
    have : c - (Z x0 : ℝ) - (0 : ℝ) / 2 = c - (Z x0 : ℝ) := by ring
    rwa [this] at h0
  have hdiff : (Z x1 - Z x0 : ℝ) + 1 / 2 = (c - (Z x0 : ℝ)) - (c - (Z x1 : ℝ) - 1 / 2) := by ring
  have h_tri : |(Z x1 - Z x0 : ℝ) + 1 / 2| ≤ |c - (Z x0 : ℝ)| + |c - (Z x1 : ℝ) - 1 / 2| := by
    rw [hdiff]
    have := abs_sub (c - (Z x0 : ℝ)) (c - (Z x1 : ℝ) - 1 / 2)
    exact this
  have h_bound : |(Z x1 - Z x0 : ℝ) + 1 / 2| ≤ 2 * ε := by linarith
  have h_half : (1 / 2 : ℝ) ≤ |(Z x1 - Z x0 : ℝ) + 1 / 2| := by
    have int_abs_two_mul_add_one_ge_one : ∀ m : ℤ, 1 ≤ |2 * m + 1| := by
      intro m
      rcases le_or_gt 0 m with h | h
      · have : 0 < 2 * m + 1 := by omega
        rw [abs_of_pos this]; omega
      · have : 2 * m + 1 < 0 := by omega
        rw [abs_of_neg this]; omega
    have : (Z x1 - Z x0 : ℝ) + 1 / 2 = ((2 * (Z x1 - Z x0) + 1 : ℤ) : ℝ) / 2 := by push_cast; ring
    rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
    have h1 := int_abs_two_mul_add_one_ge_one (Z x1 - Z x0)
    exact_mod_cast h1
  linarith

/-- OP-729 base case n = 2 for degree-0 torus approximation error. -/
theorem op_729_case_n_two (f : (Fin 2 → Bool) → Bool) :
    optimalTorusError f 0 = predictedTorusError 2 f ∧
    HasRationalTorusApproximation f 0 (predictedTorusError 2 f) := by
  rw [op_729_case_n_two_predicted_two]
  by_cases hconst : (∀ x, f x = false) ∨ (∀ x, f x = true)
  · have hanf : boolAnfCoefficient f Finset.univ = false ∧ boolNextToTopAnfCount f = 0 :=
      (op_729_case_n_two_anf_cond_iff_const f).mpr hconst
    rw [if_pos hanf]
    rcases hconst with hf | ht
    · refine ⟨op_729_case_n_two_opt_zero f (op_729_case_n_two_hasTorus_zero_of_false f hf),
              op_729_case_n_two_hasRat_zero_of_false f hf⟩
    · refine ⟨op_729_case_n_two_opt_zero f (op_729_case_n_two_hasTorus_zero_of_true f ht),
              op_729_case_n_two_hasRat_zero_of_true f ht⟩
  · have hnot : ¬ (boolAnfCoefficient f Finset.univ = false ∧ boolNextToTopAnfCount f = 0) := by
      intro h
      exact hconst ((op_729_case_n_two_anf_cond_iff_const f).mp h)
    rw [if_neg hnot]
    have hx0 : ∃ x, f x = false := by
      by_contra hc
      have : ∀ x, f x = true := fun x => by
        cases hfx : f x
        · exfalso; exact hc ⟨x, hfx⟩
        · rfl
      exact hconst (Or.inr this)
    have hx1 : ∃ x, f x = true := by
      by_contra hc
      have : ∀ x, f x = false := fun x => by
        cases hfx : f x
        · rfl
        · exfalso; exact hc ⟨x, hfx⟩
      exact hconst (Or.inl this)
    rcases hx0 with ⟨x0, hf0⟩
    rcases hx1 with ⟨x1, hf1⟩
    have hopt : optimalTorusError f 0 = 1 / 4 := by
      unfold optimalTorusError
      apply IsLeast.csInf_eq
      refine ⟨op_729_case_n_two_hasTorus_quarter f, ?_⟩
      intro ε hε
      exact op_729_case_n_two_opt_ge_quarter f x0 x1 hf0 hf1 ε hε
    exact ⟨hopt, op_729_case_n_two_hasRat_quarter f⟩
