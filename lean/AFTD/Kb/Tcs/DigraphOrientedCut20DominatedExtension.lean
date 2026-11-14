import AFTD.Prelude

/-!
# digraph_oriented_cut20_dominated_extension

Topic: graphs   Node: afba70318a99

Provenance: helper lemma. Finite extension in experiment 26335.

The explicit oriented 20-cut example extended by a 19-vertex quadratic-residue tournament; all other cross arcs point from the tournament to the part.
-/

def digraph_oriented_cut20_dominated_extension : Digraph (Fin 39) := ⟨fun u v =>
  (u.val < 5 ∧ (v.val < u.val ∨ v.val = 5 ∨ (20 ≤ v.val ∧ u.val + v.val < 26))) ∨
  (u.val = 5 ∧ 13 ≤ v.val ∧ v.val < 20) ∨
  (6 ≤ u.val ∧ u.val < 13 ∧ (v.val < 6 ∨ v.val = 6 + (u.val - 6 + 1) % 7)) ∨
  (13 ≤ u.val ∧ u.val < 20 ∧ ((13 ≤ v.val ∧ v.val < u.val) ∨ (6 ≤ v.val ∧ u.val + v.val < 26))) ∨
  (20 ≤ u.val ∧ 20 ≤ v.val ∧ (v.val + 19 - u.val) % 19 ∈ ({1,4,5,6,7,9,11,16,17} : Finset ℕ)) ∨
  (20 ≤ u.val ∧ v.val < 20 ∧ ¬ (v.val < 5 ∧ v.val + u.val < 26))⟩
