import AFTD.Prelude

/-!
# hash_insert_step

Topic: data_structures   Node: 062685b15f4c

Provenance: formalization of a published result. Source: arXiv:2610.31363 Section 2

Given table size n, an offset sequence r : Fin n → ZMod n, a set of occupied slots T : Finset (ZMod n), and an element a : ZMod n, hash_insert_step n r T a is the updated set of occupied slots in Finset (ZMod n) obtained by adding a + r(j) to T for the minimal index j : Fin n such that a + r(j) ∉ T, or returning T unchanged if no such candidate index exists.
-/

/-- One step of open addressing hash table insertion with fixed offset sequence. -/
def hash_insert_step (n : ℕ) (r : Fin n → ZMod n) (T : Finset (ZMod n)) (a : ZMod n) : Finset (ZMod n) :=
  let candidates := Finset.univ.filter (fun j : Fin n => a + r j ∉ T)
  if h : candidates.Nonempty then
    T ∪ {a + r (candidates.min' h)}
  else
    T
