import AFTD.Prelude

/-!
# uniform_kserver_total_weight

Topic: online_algorithms   Node: ba82006a16a3

Provenance: formalization of a published result. Source: arXiv:2610.37192 Section 3.1

For a natural number k, a family of spaces M indexed by Fin k, and a finitely supported weight function ϕ on configurations, uniform_kserver_total_weight ϕ is the total weight, defined as the sum of ϕ x over all configurations x in its support.
-/

/-- Total weight of a finitely supported weight function on configurations. -/
noncomputable def uniform_kserver_total_weight {k : ℕ} {M : Fin k → Type*}
    (ϕ : (∀ i, M i) →₀ ℝ) : ℝ := ϕ.sum fun _ c => c
