import AFTD.Prelude

/-!
# sages_row_edge_set

Topic: combinatorial_games   Node: 2b70fb82c86f

Provenance: helper lemma. step towards sages_row_upper_bound_binomial

The set of adjacent pairs of sages in a row seating π of S sages: all unordered pairs {π i, π (i + 1)} with i.val + 1 < S.
-/

/-- The set of adjacent pairs (edges) of a row seating, indexed by the subtype of positions with a right neighbour. -/
def sages_row_edge_set {S : ℕ} (π : Equiv.Perm (Fin S)) : Finset (Finset (Fin S)) := Finset.univ.image fun i : {i : Fin S // i.val + 1 < S} => ({π i.1, π ⟨i.1.val + 1, i.2⟩} : Finset (Fin S))
