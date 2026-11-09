import AFTD.Prelude

/-!
# petrial_R_graph

Topic: combinatorics   Node: e71d33263c42

Provenance: formalization of a published result. Source: arXiv:2611.07503 Section 3

For any natural number m, R_m is the simple graph on the vertex type Option (Fin m × Fin 5) obtained by connecting a root vertex none to the middle vertex 2 of each of m disjoint copies of the five-vertex path graph P_5.
-/

/-- The tree R_m obtained by connecting a root vertex to the middle vertex of each of m disjoint copies of P_5. -/
def petrial_R_graph (m : ℕ) : SimpleGraph (Option (Fin m × Fin 5)) where
  Adj
    | none, none => False
    | none, some (_, v) => v = 2
    | some (_, v), none => v = 2
    | some (i₁, v₁), some (i₂, v₂) => i₁ = i₂ ∧ (SimpleGraph.pathGraph 5).Adj v₁ v₂
  symm := ⟨by
    intro a b h
    match a, b with
    | none, none => exact h
    | none, some (i, v) => exact h
    | some (i, v), none => exact h
    | some (i₁, v₁), some (i₂, v₂) =>
      obtain ⟨h1, h2⟩ := h
      exact ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨by
    intro a
    match a with
    | none => intro h; exact h
    | some (i, v) =>
      intro h
      obtain ⟨-, h2⟩ := h
      exact h2.ne rfl⟩
