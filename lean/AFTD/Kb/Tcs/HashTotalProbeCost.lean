import AFTD.Prelude

/-!
# hash_total_probe_cost

Topic: data_structures   Node: a51f9cdd46f6

Provenance: formalization of a published result. Source: arXiv:2610.31363, Section 2

For a table of size n, an offset sequence r : Fin n → ZMod n, and a list of inserted key home slots A : List (ZMod n), hash_total_probe_cost n r A is the sum of the numbers of probes used by all insertions when the keys in A are inserted sequentially into an initially empty table.
-/

/-- The total number of probes accumulated across sequential insertions of keys into an initially empty hash table under offset sequence r. -/
def hash_total_probe_cost (n : ℕ) (r : Fin n → ZMod n) (A : List (ZMod n)) : ℕ :=
  let step : Finset (ZMod n) × ℕ → ZMod n → Finset (ZMod n) × ℕ := fun state a =>
    have candidates : Finset (Fin n) := {j | a + r j ∉ state.1}
    if h : candidates.Nonempty then
      (state.1 ∪ {a + r (candidates.min' h)}, state.2 + (candidates.min' h).val + 1)
    else
      state
  (List.foldl step (∅, 0) A).2
