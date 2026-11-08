import AFTD.Prelude

/-!
# alternating_path_selected_set

Topic: graphs   Node: e66740df6cd6

Provenance: formalization of a published result. Source: arXiv:2611.06985 Section 3.2, line 359

For a simple graph C on vertex type V, a vertex ρ : V, and subsets A and T of the subtype {ρ}ᶜ, alternating_path_selected_set C ρ A T is defined as the union of T and the set of vertices a ∈ A such that a is not adjacent to any vertex b ∈ T in the induced subgraph C.induce {ρ}ᶜ.
-/

/-- The vertex set S selected by choosing T ⊆ B and all vertices in A with no neighbor in T. -/
def alternating_path_selected_set {V : Type*} (C : SimpleGraph V) (ρ : V)
    (A : Set ({ρ}ᶜ : Set V)) (T : Set ({ρ}ᶜ : Set V)) : Set ({ρ}ᶜ : Set V) := T ∪ {a ∈ A | ∀ b ∈ T, ¬ (C.induce ({ρ}ᶜ : Set V)).Adj a b}
