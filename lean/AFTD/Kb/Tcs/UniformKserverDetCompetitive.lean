import AFTD.Prelude
import AFTD.Kb.Tcs.UniformKserverDetAlgServes
import AFTD.Kb.Tcs.UniformKserverDetCost
import AFTD.Kb.Tcs.UniformKserverOpt

/-!
# uniform_kserver_det_competitive

Topic: online_algorithms   Node: d7a48db2b090

Provenance: formalization of a published result. Source: arXiv:2610.37192 Sec. 6

For a natural number k, a family of types M indexed by Fin k with decidable equality, an algorithm A : List (∀ i, M i) → (∀ i, M i), an initial configuration a : ∀ i, M i, and a real γ, uniform_kserver_det_competitive k A a γ holds if uniform_kserver_det_alg_serves A and there exists a real constant c such that for every request sequence ρ : List (∀ i, M i), the deterministic cost uniform_kserver_det_cost A a ρ is at most γ * (uniform_kserver_opt k a ρ : ℝ) + c.
-/

/-- Competitiveness of a deterministic online algorithm for generalized k-server on uniform metrics. -/
def uniform_kserver_det_competitive (k : ℕ) {M : Fin k → Type*} [∀ i, DecidableEq (M i)]
    (A : List (∀ i, M i) → (∀ i, M i)) (a : ∀ i, M i) (γ : ℝ) : Prop :=
  uniform_kserver_det_alg_serves A ∧
    ∃ c : ℝ, ∀ ρ : List (∀ i, M i),
      (uniform_kserver_det_cost A a ρ : ℝ) ≤ γ * (uniform_kserver_opt k a ρ : ℝ) + c
