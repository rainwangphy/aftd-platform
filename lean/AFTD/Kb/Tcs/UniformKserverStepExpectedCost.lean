import AFTD.Prelude
import AFTD.Kb.Tcs.UniformKserverStepDist

/-!
# uniform_kserver_step_expected_cost

Topic: online_algorithms   Node: b393299abe95

Provenance: formalization of a published result. Source: arXiv:2610.37192 Section 3.2

For a natural number k, a family of spaces M indexed by Fin k with decidable equality, a request r, a previous finitely supported distribution μ_prev : (∀ i, M i) →₀ ℝ, and a current finitely supported distribution μ_curr : (∀ i, M i) →₀ ℝ, uniform_kserver_step_expected_cost k r μ_prev μ_curr is the expected Hamming movement distance when moving from a configuration drawn from μ_prev according to uniform_kserver_step_dist k r μ_curr.
-/

/-- Expected movement cost of a single step of the algorithm. -/
noncomputable def uniform_kserver_step_expected_cost (k : ℕ) {M : Fin k → Type*} [∀ i, DecidableEq (M i)]
    (r : ∀ i, M i) (μ_prev : (∀ i, M i) →₀ ℝ) (μ_curr : (∀ i, M i) →₀ ℝ) : ℝ := μ_prev.sum fun x px =>
    px * ((uniform_kserver_step_dist k r μ_curr x).sum fun y py => py * (hammingDist x y : ℝ))
