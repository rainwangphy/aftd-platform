import AFTD.Prelude

/-!
# not_fair_binomial_anticoncentration_bound

Topic: concentration   Node: e9946609c73f

Provenance: original. Related work: refutes `fair_binomial_anticoncentration_bound`

The statement `fair_binomial_anticoncentration_bound` is false: The statement is false for small α. Take n = 2, α = 1/10, and X the identity on the binomial space Bin(2, 1/2). The interval |X - 1| ≤ (1/10)√2 contains the integer 1, whose binomial probability is C(2,1)/2^2 = 1/2. But the claimed right-hand side is 2e(1/10)/π < 1/5, since e < 3 and π > 3. Thus 1/2 ≤ 2e/(10π) fails.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval
theorem not_fair_binomial_anticoncentration_bound : ¬ (∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (X : Ω → ℕ)
    (hX : HasLaw X (binomial n ⟨1/2, by norm_num⟩) μ)
    (α : ℝ) (hα_pos : 0 < α), μ.real {ω | |(X ω : ℝ) - (n : ℝ) / 2| ≤ α * Real.sqrt (n : ℝ)} ≤
      2 * Real.exp 1 * α / Real.pi) := by
  intro h
  let p : unitInterval := ⟨1/2, by norm_num⟩
  let μ : Measure (ULift ℕ) := (binomial 2 p).map ULift.up
  let X : ULift ℕ → ℕ := ULift.down
  have hX : HasLaw X (binomial 2 p) μ := by
    dsimp [X, μ]
    refine ⟨?_, ?_⟩
    · exact measurable_down.aemeasurable
    · rw [Measure.map_map measurable_down measurable_up]
      convert Measure.map_id (μ := binomial 2 p) using 2
      funext x
      rfl
  have h' := h (Ω := ULift ℕ) (μ := μ) 2 (by norm_num) X hX (1/10) (by norm_num)
  norm_num at h'
  have hmeas : MeasurableSet {x : ℕ | |(x : ℝ) - 1| ≤ (1/10 : ℝ) * Real.sqrt (2 : ℝ)} := by
    measurability
  rw [hX.measureReal_eq (p := fun x => |(x : ℝ) - 1| ≤ (1/10 : ℝ) * Real.sqrt (2 : ℝ)) hmeas] at h'
  have hset : ({x : ℕ | |(x : ℝ) - 1| ≤ (1/10 : ℝ) * Real.sqrt (2 : ℝ)}) = {1} := by
    ext ω
    constructor
    · intro hmem
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hmem ⊢
      have hsqrt : Real.sqrt (2 : ℝ) < 2 := by
        rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
        norm_num
      have hlt : |(ω : ℝ) - 1| < 1 := by
        calc |(ω : ℝ) - 1| ≤ (1/10 : ℝ) * Real.sqrt 2 := hmem
          _ < (1/10 : ℝ) * 2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
          _ < 1 := by norm_num
      have hrange : (ω : ℝ) ∈ Set.Ioo 0 2 := by
        rw [Set.mem_Ioo]
        constructor
        · have := (abs_lt.mp hlt).1
          linarith
        · have := (abs_lt.mp hlt).2
          linarith
      have hωlt : ω < 2 := by exact_mod_cast hrange.2
      have hωpos : 0 < ω := by exact_mod_cast hrange.1
      omega
    · intro hmem
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hmem ⊢
      subst ω
      norm_num
  rw [hset] at h'
  rw [ProbabilityTheory.binomial_real_singleton] at h'
  norm_num at h'
  have hexp3 : Real.exp 1 < 3 := by
    calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ < 3 := by norm_num
  have hden : (0 : ℝ) < Real.pi := Real.pi_pos
  have hb : 2 * Real.exp 1 * (1/10) / Real.pi < 1/5 := by
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_gt_three]
  linarith
