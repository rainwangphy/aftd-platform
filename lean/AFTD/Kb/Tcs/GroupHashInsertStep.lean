import AFTD.Prelude

/-!
# group_hash_insert_step

Topic: data_structures   Node: 2cc717896387

Provenance: formalization of a published result. Source: arXiv:2610.31363; OP-808

Given a group G with decidable equality, table size n, offset sequence r : Fin n → G, a finite set of occupied slots T : Finset G, and key a : G, group_hash_insert_step n r T a is the updated set of occupied slots in Finset G obtained by adding a * r j to T for the minimal index j : Fin n such that a * r j ∉ T, or returning T unchanged if no such candidate index exists.
-/

/-- Insertion step of open addressing hash table on a finite group G using offset sequence r. -/
def group_hash_insert_step {G : Type*} [Group G] [DecidableEq G]
    (n : ℕ) (r : Fin n → G) (T : Finset G) (a : G) : Finset G :=
  let candidates := Finset.univ.filter (fun j : Fin n => a * r j ∉ T)
  if h : candidates.Nonempty then
    T ∪ {a * r (candidates.min' h)}
  else
    T
