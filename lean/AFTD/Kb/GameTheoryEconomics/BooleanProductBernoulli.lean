import AFTD.Prelude

/-!
# boolean_product_bernoulli

Topic: combinatorial_games   Node: 684a8e4ddcb8

Provenance: formalization of a published result. Source: arXiv:2610.30730 Section 2

Given a finite type $U$ and a parameter $p$ in the unit interval `unitInterval` (the closed interval $[0, 1]$), `boolean_product_bernoulli U p` is the product measure on $U \to \mathrm{Bool}$ given by `MeasureTheory.Measure.pi` where each coordinate is independently distributed according to the Bernoulli measure `ProbabilityTheory.bernoulliMeasure true false p` on $\mathrm{Bool}$ with parameter $p$.
-/

/-- The product Bernoulli measure with parameter p on the hypercube {0, 1}^U. -/
noncomputable def boolean_product_bernoulli (U : Type*) [Fintype U] (p : unitInterval) :
    MeasureTheory.Measure (U → Bool) := MeasureTheory.Measure.pi (fun _ : U ↦ ProbabilityTheory.bernoulliMeasure true false p)
