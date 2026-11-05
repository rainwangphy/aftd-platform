import AFTD.Prelude

/-!
# heap_final_perm

Topic: combinatorics   Node: 361fefb3c7f4

Provenance: formalization of a published result. Source: arXiv:2611.05397 Definition 3 and Theorem 5

The permutation of Fin m induced by the final arrangement array of the order-m Heap algorithm.
-/

/-- The permutation of `Fin m` induced by the final arrangement array of the order-`m` Heap algorithm. -/
def heap_final_perm (m : ℕ) : Equiv.Perm (Fin m) :=
  if hm : m % 2 = 1 ∧ 3 ≤ m then
    Equiv.swap ⟨0, by omega⟩ ⟨m - 1, by omega⟩
  else if h4 : 4 ≤ m then
    let zero : Fin m := ⟨0, by omega⟩
    let mid : List (Fin m) := ((List.range (m - 3)).reverse.filterMap (fun i =>
      if hi : i + 1 < m then some ⟨i + 1, hi⟩ else none))
    let penultimate : Fin m := ⟨m - 2, by omega⟩
    let last : Fin m := ⟨m - 1, by omega⟩
    List.formPerm (zero :: (mid ++ [penultimate, last]))
  else if hm2 : m = 2 then
    Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩
  else
    1
