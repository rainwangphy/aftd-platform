import AFTD.Prelude
import AFTD.Kb.Tcs.UniformKserverWeightUpdate
import AFTD.Kb.Tcs.UniformKserverTotalWeight
import AFTD.Kb.Tcs.UniformKserverStepExpectedCost

/-!
# uniform_kserver_expected_cost

Topic: online_algorithms   Node: 088fea33a27b

Provenance: formalization of a published result. Source: arXiv:2610.37192 Section 3.2

For a natural number k, a family of spaces M indexed by Fin k with decidable equality, an initial configuration a, and a list of requests ρ, uniform_kserver_expected_cost k a ρ is the total expected movement cost of the randomized online tracking algorithm starting from a on request sequence ρ.
-/

/-- Expected movement cost of the randomized algorithm over a request sequence. -/
noncomputable def uniform_kserver_expected_cost (k : ℕ) {M : Fin k → Type*} [∀ i, DecidableEq (M i)]
    (a : ∀ i, M i) (ρ : List (∀ i, M i)) : ℝ := (ρ.foldl (fun (acc : ℝ × ((∀ i, M i) →₀ ℝ)) (r : ∀ i, M i) =>
    let ϕ_next := uniform_kserver_weight_update k r acc.2
    let W := uniform_kserver_total_weight ϕ_next
    let μ_next := (1 / W) • ϕ_next
    let step_cost := uniform_kserver_step_expected_cost k r ((1 / uniform_kserver_total_weight acc.2) • acc.2) μ_next
    (acc.1 + step_cost, ϕ_next))
    (0, Finsupp.single a 1)).1
