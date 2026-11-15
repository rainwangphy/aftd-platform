import AFTD.Prelude

/-!
# dephased_path_active_edge

Topic: quantum_mechanics   Node: f3bf6b3d2fbe

Provenance: helper lemma. step towards dephased_path_unpinned_intervals_add_greedy_matching

For a path on n vertices with vertex sets I, D ⊆ ℕ and end pin flags left, right, the activity flag of the cut edge at position e: the end edges e = 0 and e = n are active when the corresponding pin flag is set and the adjacent vertex 0, resp. n-1, lies in I ∩ D; an interior edge e is active when exactly one of e-1, e lies in I ∩ D and the other lies outside I.
-/

open scoped Classical in
/-- Activity flag of the cut edge at position e; an interior edge is active iff its endpoints are split by I ∩ D. -/
def dephased_path_active_edge (n : ℕ) (I D : Finset ℕ) (left right : Bool) (e : ℕ) : Bool := if e = 0 then left && decide (0 ∈ I ∧ 0 ∈ D)
  else if e = n then right && decide (n - 1 ∈ I ∧ n - 1 ∈ D)
  else decide (((e - 1 ∈ I ∧ e - 1 ∈ D) ∧ e ∉ I) ∨ ((e ∈ I ∧ e ∈ D) ∧ e - 1 ∉ I))
