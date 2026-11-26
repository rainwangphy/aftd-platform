import AFTD.Prelude

/-!
# is_cycle_factor

Topic: combinatorics   Node: 4b3b7defe0c4

Provenance: formalization of a published result. Source: arXiv:2611.34299 Section 1

A simple graph is a uniform cycle factor of length ℓ (a C_ℓ-factor) if each of its connected components is isomorphic to the cycle graph of length ℓ.
-/

/-- A simple graph is a C_ℓ-factor if each of its connected components is isomorphic to the cycle graph of length ℓ. -/
def is_cycle_factor {V : Type*} (G : SimpleGraph V) (ℓ : ℕ) : Prop := ∀ c : G.ConnectedComponent, Nonempty (G.induce c.supp ≃g SimpleGraph.cycleGraph ℓ)
