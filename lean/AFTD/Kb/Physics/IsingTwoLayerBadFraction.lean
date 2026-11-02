import AFTD.Prelude
import AFTD.Kb.Physics.IsingTwoLayerGibbsExpectation
import AFTD.Kb.Physics.IsingTwoLayerQuarticExpectation

/-!
# ising_two_layer_bad_fraction

Topic: statistical_mechanics   Node: 525692770494

Provenance: helper lemma. Auxiliary definition for OP-812, critical two-layer random regular Ising crossover.

Among all ordered pairs of simple d-regular graphs on Fin n, the fraction whose Gibbs expectation differs from the target expectation by at least ε.
-/

open scoped BigOperators
open MeasureTheory

noncomputable def ising_two_layer_bad_fraction (d n : ℕ) (c ε : ℝ)
    (f : BoundedContinuousFunction (ℝ × ℝ) ℝ) : ℝ := by
  classical
  let pairs : Finset (SimpleGraph (Fin n) × SimpleGraph (Fin n)) :=
    Finset.univ.filter (fun p => p.1.IsRegularOfDegree d ∧ p.2.IsRegularOfDegree d)
  exact ((pairs.filter (fun p => ε ≤ |ising_two_layer_gibbs_expectation d n c p.1 p.2 f -
    ising_two_layer_quartic_expectation d c f|)).card : ℝ) / (pairs.card : ℝ)
