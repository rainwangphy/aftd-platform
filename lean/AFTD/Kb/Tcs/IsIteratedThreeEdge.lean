import AFTD.Prelude

/-!
# is_iterated_three_edge

Topic: combinatorics   Node: 635a80857e1e

Provenance: formalization of a published result. Source: arXiv:2610.14829 Section 2.2

A 3-element subset e of vertices in (Fin d → Fin 3) is an edge of the d-times iterated blow-up of a single 3-edge if there exists a coordinate ℓ in Fin d such that all vertices in e agree on all coordinates strictly less than ℓ, and any two distinct vertices in e have different values at coordinate ℓ.
-/

/-- An edge of the d-times iterated blow-up of a 3-edge (K_3^{(3)})^d on Fin d → Fin 3: a triple of vertices agreeing below level ℓ and pairwise distinct at level ℓ. -/
def is_iterated_three_edge (d : ℕ) (e : Finset (Fin d → Fin 3)) : Prop :=
  e.card = 3 ∧
  ∃ ℓ : Fin d,
    (∀ u ∈ e, ∀ v ∈ e, ∀ i : Fin d, i < ℓ → u i = v i) ∧
    (∀ u ∈ e, ∀ v ∈ e, u ≠ v → u ℓ ≠ v ℓ)
