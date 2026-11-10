import AFTD.Prelude

/-!
# finite_ten_seed_four_books_certificate

Topic: graphs   Node: 86a62f4d3644

Provenance: helper lemma. Finite four-book classification certificate in the internal-anchor triangle-packing campaign, experiment 20598.

For the specified ten-vertex, twenty-edge seed, every outside triangle except a page on the four listed cycle edges has an explicitly listed six-packing witness.
-/

open scoped Sym2
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def in694ten_edges : Finset (Sym2 (Fin 11)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(1,7),s(2,3),s(2,4),s(2,6),s(2,7),s(2,9),s(3,4),s(3,5),s(3,7),s(3,8),s(4,5),s(4,6),s(7,8),s(7,9)}

def in694ten_triangle (t : Fin 11 × Fin 11 × Fin 11) : Finset (Sym2 (Fin 11)) :=
  {s(t.1,t.2.1), s(t.1,t.2.2), s(t.2.1,t.2.2)}

def in694ten_valid (Q : List (Fin 11 × Fin 11 × Fin 11)) (E : Finset (Sym2 (Fin 11))) : Bool :=
  (Q.length == 6) && Q.all (fun t => decide (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ in694ten_triangle t ⊆ E)) &&
  Q.all (fun t => Q.all (fun u => decide (t = u ∨ Disjoint (in694ten_triangle t) (in694ten_triangle u)))) && decide Q.Nodup

def in694ten_witness (i j : Fin 11) : List (Fin 11 × Fin 11 × Fin 11) :=
  if i = 0 ∧ j = 1 then [(2,7,9),(3,7,8),(0,1,10),(1,2,3),(2,4,6),(0,3,4)] else
  if i = 0 ∧ j = 2 then [(2,7,9),(3,7,8),(0,3,4),(2,4,6),(1,2,3),(0,2,10)] else
  if i = 0 ∧ j = 3 then [(2,7,9),(3,7,8),(3,4,5),(2,4,6),(0,3,10),(0,1,2)] else
  if i = 0 ∧ j = 4 then [(2,7,9),(3,7,8),(0,4,10),(3,4,5),(2,4,6),(0,1,2)] else
  if i = 0 ∧ j = 5 then [(0,5,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 0 ∧ j = 6 then [(2,7,9),(3,7,8),(0,6,10),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 0 ∧ j = 7 then [(0,3,4),(2,4,6),(0,7,10),(2,7,9),(0,1,2),(3,7,8)] else
  if i = 0 ∧ j = 8 then [(0,8,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 0 ∧ j = 9 then [(0,9,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 1 ∧ j = 2 then [(2,7,9),(3,7,8),(1,2,10),(0,1,3),(3,4,5),(2,4,6)] else
  if i = 1 ∧ j = 3 then [(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2),(1,3,10)] else
  if i = 1 ∧ j = 4 then [(2,7,9),(3,7,8),(1,4,10),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 1 ∧ j = 5 then [(1,5,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 1 ∧ j = 6 then [(1,2,6),(2,7,9),(3,7,8),(0,1,3),(3,4,5),(0,2,4)] else
  if i = 1 ∧ j = 7 then [(2,7,9),(1,7,10),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 1 ∧ j = 8 then [(2,7,9),(0,3,4),(2,4,6),(0,1,2),(1,8,10),(3,7,8)] else
  if i = 1 ∧ j = 9 then [(1,9,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 2 ∧ j = 3 then [(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2),(2,3,10)] else
  if i = 2 ∧ j = 5 then [(2,7,9),(3,7,8),(2,5,10),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 2 ∧ j = 6 then [(2,6,10),(2,7,9),(3,7,8),(3,4,5),(0,2,4),(0,1,3)] else
  if i = 2 ∧ j = 8 then [(2,3,8),(2,7,9),(1,3,7),(0,3,4),(0,1,2),(2,4,6)] else
  if i = 2 ∧ j = 9 then [(2,9,10),(3,4,5),(2,4,6),(3,7,8),(1,2,7),(0,1,3)] else
  if i = 3 ∧ j = 5 then [(3,5,10),(2,7,9),(3,7,8),(2,4,6),(0,3,4),(0,1,2)] else
  if i = 3 ∧ j = 6 then [(2,7,9),(3,7,8),(3,6,10),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 3 ∧ j = 8 then [(3,8,10),(2,7,9),(1,3,7),(0,3,4),(0,1,2),(2,4,6)] else
  if i = 3 ∧ j = 9 then [(3,9,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 4 ∧ j = 5 then [(4,5,10),(2,7,9),(3,7,8),(2,4,6),(0,3,4),(0,1,2)] else
  if i = 4 ∧ j = 6 then [(4,6,10),(2,7,9),(3,7,8),(3,4,5),(0,2,4),(0,1,3)] else
  if i = 4 ∧ j = 7 then [(4,7,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 4 ∧ j = 8 then [(4,8,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 4 ∧ j = 9 then [(4,9,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 5 ∧ j = 6 then [(5,6,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 5 ∧ j = 7 then [(5,7,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 5 ∧ j = 8 then [(5,8,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 5 ∧ j = 9 then [(5,9,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 6 ∧ j = 7 then [(6,7,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 6 ∧ j = 8 then [(6,8,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  if i = 6 ∧ j = 9 then [(2,6,9),(3,4,5),(0,2,4),(0,1,3),(3,7,8),(1,2,7)] else
  if i = 7 ∧ j = 8 then [(7,8,10),(2,7,9),(1,3,7),(0,3,4),(0,1,2),(2,4,6)] else
  if i = 7 ∧ j = 9 then [(7,9,10),(3,4,5),(2,4,6),(3,7,8),(1,2,7),(0,1,3)] else
  if i = 8 ∧ j = 9 then [(8,9,10),(2,7,9),(3,7,8),(0,3,4),(2,4,6),(0,1,2)] else
  []

theorem finite_ten_seed_four_books_certificate :
    ∀ i j : Fin 11, i.val < 10 → j.val < 10 → i < j →
      s(i,j) ≠ s(2,4) → s(i,j) ≠ s(2,7) → s(i,j) ≠ s(3,4) → s(i,j) ≠ s(3,7) →
      in694ten_valid (in694ten_witness i j) (insert s(i,j) (insert s(i,10) (insert s(j,10) in694ten_edges))) = true := by
  decide
