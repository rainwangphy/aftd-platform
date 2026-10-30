import AFTD.Prelude
import AFTD.Kb.Tcs.UniformKserverOfflineCost
import AFTD.Kb.Tcs.UniformKserverDetSchedule

/-!
# uniform_kserver_det_cost

Topic: online_algorithms   Node: 40b01e8d289c

Provenance: formalization of a published result. Source: arXiv:2610.37192 Sec. 6

For a natural number k, a family of types M indexed by Fin k with decidable equality, an algorithm A : List (∀ i, M i) → (∀ i, M i), an initial configuration a : ∀ i, M i, and a request sequence ρ : List (∀ i, M i), uniform_kserver_det_cost A a ρ is the offline movement cost uniform_kserver_offline_cost a (uniform_kserver_det_schedule A ρ).
-/

/-- Total movement cost incurred by deterministic algorithm A on ρ starting from a. -/
def uniform_kserver_det_cost {k : ℕ} {M : Fin k → Type*} [∀ i, DecidableEq (M i)]
    (A : List (∀ i, M i) → (∀ i, M i)) (a : ∀ i, M i) (ρ : List (∀ i, M i)) : ℕ :=
  uniform_kserver_offline_cost a (uniform_kserver_det_schedule A ρ)
