import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BonamiUniformMeasure

/-!
# Bonami.uniformMeasure_apply

Topic: combinatorics   Node: 60860a60379d

Provenance: helper lemma. TCSlib, `Bonami.uniformMeasure_apply`. Lean proof by Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean (Apache-2.0); 1 verbatim; compiled here.

Uniform measure of a single point of the hypercube. Let $n$ be a natural number and let $x$ be a point of the Boolean hypercube $\{0,1\}^n$.
Under the canonical uniform probability measure on $\{0,1\}^n$, the measure of the
singleton $\{x\}$, taken as a real number, equals the uniform weight $2^{-n}$.
-/

open BooleanAnalysis in
open MeasureTheory Set Filter ProbabilityTheory BooleanAnalysis Real in
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] in
/-- Prove that our canonical measure matches the combinatorial uniformWeight. **Source:** [OD14, Cor. 9.6 (uniform product-space specialization)]. -/
lemma Bonami.uniformMeasure_apply {n : ℕ} (x : BoolCube n) :
    ((uniformMeasure n) {x}).toReal = uniformWeight n := by
  dsimp [uniformMeasure]
  rw [PMF.toMeasure_apply_singleton]
  simp only [PMF.uniformOfFintype_apply]
  rw [ENNReal.toReal_inv]
  simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold uniformWeight
  rw[ENNReal.toReal_natCast]
  simp only [Nat.cast_pow, Nat.cast_ofNat, inv_pow]
  exact MeasurableSet.singleton x
