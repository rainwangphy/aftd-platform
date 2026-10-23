import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BooleanProductBernoulli

/-!
# boolean_product_bernoulli_isProbabilityMeasure

Topic: combinatorial_games   Node: 7d337dc0862e

Provenance: formalization of a published result. Source: arXiv:2610.30730 Section 2

For any finite type $U$ and parameter $p \in [0, 1]$ in `unitInterval`, the product Bernoulli measure `boolean_product_bernoulli U p` on $U \to \mathrm{Bool}$ is a probability measure.
-/

/-- The product Bernoulli measure is a probability measure. -/
instance boolean_product_bernoulli_isProbabilityMeasure (U : Type*) [Fintype U] (p : unitInterval) :
    MeasureTheory.IsProbabilityMeasure (boolean_product_bernoulli U p) := by dsimp [boolean_product_bernoulli]; infer_instance
