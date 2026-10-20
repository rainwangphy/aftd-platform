import AFTD.Prelude

/-!
# galvin_conflict_arc

Topic: combinatorics   Node: 5b1efbf62fc0

Provenance: helper lemma. step towards galvin_bipartite_multigraph_list_edge_colouring

Galvin's orientation of the conflict graph of a properly edge-coloured bipartite multigraph, in fibre form. Read f e as the left endpoint (part X) and g e as the right endpoint (part Y). Two edges conflict when they are distinct and share a left or a right endpoint. At a shared left endpoint arcs go from the larger colour m to the smaller; at a shared right endpoint from the smaller colour to the larger. On a pair of parallel edges (same f and same g) both disjuncts fire, so such a pair carries a digon -- this is deliberate and necessary.
-/

/-- Galvin's orientation of the line graph of a properly edge-coloured bipartite multigraph (f = left endpoint, g = right endpoint, digons kept on parallel edges). -/
def galvin_conflict_arc {α : Type*} (f g m : α → ℕ) (e₁ e₂ : α) : Prop := e₁ ≠ e₂ ∧ ((f e₁ = f e₂ ∧ m e₂ < m e₁) ∨ (g e₁ = g e₂ ∧ m e₁ < m e₂))
