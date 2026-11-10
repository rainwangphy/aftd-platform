import AFTD.Prelude

/-!
# finite_nine_seed_two_books_certificate

Topic: graphs   Node: 91f03afd7e97

Provenance: helper lemma. Finite two-book classification certificate in the internal-anchor triangle-packing campaign, experiment 20594.

For the specified nine-vertex, twenty-edge seed, each outside triangle except one based on 26 or 34 has an explicitly listed six-packing witness.
-/

open scoped Sym2
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def in694nine_edges : Finset (Sym2 (Fin 10)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(1,6),s(2,3),s(2,4),s(2,6),s(2,7),s(2,8),s(3,4),s(3,5),s(3,6),s(3,7),s(4,5),s(4,7),s(6,7),s(6,8)}

def in694nine_triangle (t : Fin 10 × Fin 10 × Fin 10) : Finset (Sym2 (Fin 10)) :=
  {s(t.1,t.2.1), s(t.1,t.2.2), s(t.2.1,t.2.2)}

def in694nine_valid (Q : List (Fin 10 × Fin 10 × Fin 10)) (E : Finset (Sym2 (Fin 10))) : Bool :=
  (Q.length == 6) && Q.all (fun t => decide (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ in694nine_triangle t ⊆ E)) &&
  Q.all (fun t => Q.all (fun u => decide (t = u ∨ Disjoint (in694nine_triangle t) (in694nine_triangle u)))) && decide Q.Nodup

def in694nine_witness (i j : Fin 10) : List (Fin 10 × Fin 10 × Fin 10) :=
  if i = 0 ∧ j = 1 then [(0,1,9),(0,3,4),(2,4,7),(3,6,7),(2,6,8),(1,2,3)] else
  if i = 0 ∧ j = 2 then [(0,2,9),(0,3,4),(2,4,7),(3,6,7),(2,6,8),(1,2,3)] else
  if i = 0 ∧ j = 3 then [(0,3,9),(3,4,5),(0,1,2),(2,3,7),(1,3,6),(2,6,8)] else
  if i = 0 ∧ j = 4 then [(0,4,9),(3,4,5),(2,3,7),(2,6,8),(0,1,2),(1,3,6)] else
  if i = 0 ∧ j = 5 then [(0,5,9),(0,3,4),(2,3,7),(1,3,6),(0,1,2),(2,6,8)] else
  if i = 0 ∧ j = 6 then [(0,6,9),(0,3,4),(2,3,7),(1,3,6),(0,1,2),(2,6,8)] else
  if i = 0 ∧ j = 7 then [(1,2,6),(2,3,7),(0,1,3),(3,4,5),(0,7,9),(0,2,4)] else
  if i = 0 ∧ j = 8 then [(0,2,8),(0,1,3),(1,2,6),(3,6,7),(3,4,5),(2,4,7)] else
  if i = 1 ∧ j = 2 then [(2,6,8),(1,2,9),(1,3,6),(3,4,5),(2,3,7),(0,2,4)] else
  if i = 1 ∧ j = 3 then [(1,2,6),(1,3,9),(3,6,7),(2,4,7),(3,4,5),(0,2,3)] else
  if i = 1 ∧ j = 4 then [(1,2,6),(2,3,7),(0,2,4),(1,4,9),(0,1,3),(3,4,5)] else
  if i = 1 ∧ j = 5 then [(1,5,9),(0,3,4),(2,3,7),(1,3,6),(0,1,2),(2,6,8)] else
  if i = 1 ∧ j = 6 then [(1,6,9),(2,6,8),(2,3,7),(3,4,5),(0,1,3),(0,2,4)] else
  if i = 1 ∧ j = 7 then [(1,2,6),(1,7,9),(2,3,7),(0,1,3),(3,4,5),(0,2,4)] else
  if i = 1 ∧ j = 8 then [(1,8,9),(0,3,4),(2,3,7),(1,3,6),(0,1,2),(2,6,8)] else
  if i = 2 ∧ j = 3 then [(1,2,6),(3,6,7),(2,3,9),(0,1,3),(3,4,5),(2,4,7)] else
  if i = 2 ∧ j = 4 then [(2,6,8),(1,3,6),(0,1,2),(2,4,9),(2,3,7),(0,3,4)] else
  if i = 2 ∧ j = 5 then [(2,4,5),(0,3,4),(0,1,2),(1,3,6),(2,3,7),(2,6,8)] else
  if i = 2 ∧ j = 7 then [(2,7,9),(1,2,6),(3,6,7),(0,1,3),(3,4,5),(0,2,4)] else
  if i = 2 ∧ j = 8 then [(2,8,9),(3,4,5),(0,2,3),(2,4,7),(1,2,6),(3,6,7)] else
  if i = 3 ∧ j = 5 then [(3,5,9),(2,6,8),(1,3,6),(0,1,2),(0,3,4),(2,3,7)] else
  if i = 3 ∧ j = 6 then [(3,6,9),(1,2,6),(0,1,3),(0,2,4),(2,3,7),(3,4,5)] else
  if i = 3 ∧ j = 7 then [(3,7,9),(0,3,4),(2,4,7),(0,1,2),(1,3,6),(2,6,8)] else
  if i = 3 ∧ j = 8 then [(2,3,8),(3,4,5),(3,6,7),(1,2,6),(0,1,3),(2,4,7)] else
  if i = 4 ∧ j = 5 then [(4,5,9),(2,6,8),(1,3,6),(0,1,2),(0,3,4),(2,3,7)] else
  if i = 4 ∧ j = 6 then [(4,6,7),(0,3,4),(0,1,2),(1,3,6),(2,3,7),(2,6,8)] else
  if i = 4 ∧ j = 7 then [(4,7,9),(0,3,4),(0,1,2),(1,3,6),(2,3,7),(2,6,8)] else
  if i = 4 ∧ j = 8 then [(4,8,9),(0,3,4),(2,3,7),(1,3,6),(0,1,2),(2,6,8)] else
  if i = 5 ∧ j = 6 then [(5,6,9),(0,3,4),(2,3,7),(1,3,6),(0,1,2),(2,6,8)] else
  if i = 5 ∧ j = 7 then [(4,5,7),(2,6,8),(2,3,7),(1,3,6),(0,3,4),(0,1,2)] else
  if i = 5 ∧ j = 8 then [(5,8,9),(0,3,4),(2,3,7),(1,3,6),(0,1,2),(2,6,8)] else
  if i = 6 ∧ j = 7 then [(6,7,9),(1,2,6),(0,1,3),(0,2,4),(2,3,7),(3,4,5)] else
  if i = 6 ∧ j = 8 then [(6,8,9),(3,4,5),(0,2,3),(2,4,7),(1,2,6),(3,6,7)] else
  if i = 7 ∧ j = 8 then [(7,8,9),(0,3,4),(2,3,7),(1,3,6),(0,1,2),(2,6,8)] else
  []

theorem finite_nine_seed_two_books_certificate :
    ∀ i j : Fin 10, i.val < 9 → j.val < 9 → i < j →
      s(i,j) ≠ s(2,6) → s(i,j) ≠ s(3,4) →
      in694nine_valid (in694nine_witness i j) (insert s(i,j) (insert s(i,9) (insert s(j,9) in694nine_edges))) = true := by
  decide
