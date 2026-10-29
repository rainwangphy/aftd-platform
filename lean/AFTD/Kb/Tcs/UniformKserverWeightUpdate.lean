import AFTD.Prelude
import AFTD.Kb.Tcs.UniformKserverServes

/-!
# uniform_kserver_weight_update

Topic: online_algorithms   Node: a7afc5a67fbd

Provenance: formalization of a published result. Source: arXiv:2610.37192 Section 3.1 (1)

For a natural number k, a family of spaces M indexed by Fin k with decidable equality, a request r, and a finitely supported weight function ϕ on configurations, uniform_kserver_weight_update k r ϕ is the updated finitely supported weight function where configurations serving r retain their weight, and each configuration x failing r retains zero weight at x, discards half of its weight, and distributes a 1/(2k) fraction of its weight to each of its k repairs Function.update x i (r i).
-/

/-- Weight update operator for generalized k-server on uniform metrics. -/
noncomputable def uniform_kserver_weight_update (k : ℕ) {M : Fin k → Type*} [∀ i, DecidableEq (M i)]
    (r : ∀ i, M i) (ϕ : (∀ i, M i) →₀ ℝ) : (∀ i, M i) →₀ ℝ := by
  classical
  exact ϕ.sum fun x c =>
    if uniform_kserver_serves x r then
      Finsupp.single x c
    else
      ∑ i : Fin k, Finsupp.single (Function.update x i (r i)) (c / (2 * (k : ℝ)))
