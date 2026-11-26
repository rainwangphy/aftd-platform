import AFTD.Prelude

/-!
# op309_rook_uncovered_count

Topic: graphs   Node: 01998370ff08

Provenance: helper lemma. OP-309 six-vertex maximum-uncovered obstruction.

Count unused row and column vertices of a set of edges in the three-by-three complete bipartite incidence array.
-/

def op309_rook_uncovered_count (R : Finset (Fin 3 × Fin 3)) : ℕ := (Finset.univ.filter fun i : Fin 3 => ∀ j : Fin 3, (i,j) ∉ R).card +
    (Finset.univ.filter fun j : Fin 3 => ∀ i : Fin 3, (i,j) ∉ R).card
