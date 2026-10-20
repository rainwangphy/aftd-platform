import AFTD.Prelude

/-!
# is_balanced_five_coloring

Topic: combinatorics   Node: c637d6c04634

Provenance: formalization of a published result. Source: scout/2610-24484-erd-h-o-s-gy-arf-as-balanced-five-colorings.md:1263

For an arbitrary type V, an edge coloring c : Sym2 V → Fin 5 is balanced if for every 6-element subset S : Finset V with S.card = 6 and every color k : Fin 5, there exist distinct vertices v, w ∈ S such that c(s(v, w)) = k.
-/

/-- A 5-coloring of the edges of a complete graph is balanced if every 6 vertices span all 5 colors. -/
def is_balanced_five_coloring {V : Type*} (c : Sym2 V → Fin 5) : Prop :=
  ∀ S : Finset V, S.card = 6 → ∀ k : Fin 5, ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ c s(v, w) = k
