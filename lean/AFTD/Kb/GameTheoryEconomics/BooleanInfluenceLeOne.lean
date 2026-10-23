import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BooleanInfluence
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.BooleanProductBernoulli
import AFTD.Kb.GameTheoryEconomics.BooleanProductBernoulliIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# boolean_influence_le_one

Topic: combinatorial_games   Node: d903b071a402

Provenance: helper lemma. arXiv:2610.30730 Lemma 2.1

For any finite type $U$ with decidable equality, monotone Boolean function $f : (U \to \mathrm{Bool}) \to \mathrm{Bool}$, coordinate $i \in U$, and parameter $p$ in `unitInterval`, `boolean_influence U f i p` is at most 1.
-/

/-- The influence of any coordinate on a monotone Boolean function is at most 1. -/
lemma boolean_influence_le_one (U : Type*) [Fintype U] [DecidableEq U]
    (f : (U → Bool) → Bool) (hf : Monotone f) (i : U) (p : unitInterval) :
    boolean_influence U f i p ≤ 1 := by
  have hpt : ∀ x : U → Bool,
      (if f (Function.update x i true) then (1:ℝ) else 0) -
        (if f (Function.update x i false) then 1 else 0) ≤ 1 := by
    intro x
    have hle : Function.update x i false ≤ Function.update x i true := by
      intro j
      by_cases h : j = i
      · subst h; simp [Function.update]
      · simp [Function.update, h]
    have hmono : f (Function.update x i false) ≤ f (Function.update x i true) := hf hle
    cases h1 : f (Function.update x i true)
    · have h2 : f (Function.update x i false) = false := by
        have hle' : f (Function.update x i false) ≤ false := by rw [h1] at hmono; exact hmono
        exact le_antisymm hle' (Bool.false_le _)
      simp [h2]
    · cases h2 : f (Function.update x i false)
      · simp
      · simp
  have hint1 : MeasureTheory.Integrable
      (fun x : U → Bool =>
        (if f (Function.update x i true) then (1:ℝ) else 0) -
          (if f (Function.update x i false) then 1 else 0))
      (boolean_product_bernoulli U p) := MeasureTheory.Integrable.of_finite
  have hint2 : MeasureTheory.Integrable (fun _ : U → Bool => (1:ℝ))
      (boolean_product_bernoulli U p) := MeasureTheory.Integrable.of_finite
  have hmono_int := MeasureTheory.integral_mono hint1 hint2 hpt
  have hconst : ∫ (_ : U → Bool), (1:ℝ) ∂boolean_product_bernoulli U p = 1 := by
    rw [MeasureTheory.integral_const]; simp
  unfold boolean_influence
  rw [hconst] at hmono_int
  exact hmono_int
