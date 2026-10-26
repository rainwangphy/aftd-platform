import AFTD.Prelude
import AFTD.Kb.Tcs.GraphHomDensity
import AFTD.Kb.Tcs.IsLocallyDense

/-!
# is_knrs

Topic: graphs   Node: ae4982b19d89

Provenance: formalization of a published result. Source: arXiv:2610.13820, Conjecture 1.1

A graph F has the KNRS property if for every d in (0, 1] and every ε > 0, there exists ρ > 0 and n₀ such that every (ρ, d)-dense graph G on at least n₀ vertices has homomorphism density q(F, G) ≥ d^{e(F)} - ε.
-/

/-- The KNRS property for a graph F: homomorphism density in locally dense graphs is asymptotically bounded below by d^{e(F)}. -/
def is_knrs {α : Type*} [Fintype α] (F : SimpleGraph α) : Prop := ∀ (d : ℝ), 0 < d → d ≤ 1 → ∀ (ε : ℝ), 0 < ε →
    ∃ (ρ : ℝ), 0 < ρ ∧ ∃ (n₀ : ℕ), ∀ (n : ℕ), n₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)), is_locally_dense G ρ d →
        d ^ (Nat.card F.edgeSet) - ε ≤ graph_hom_density F G
