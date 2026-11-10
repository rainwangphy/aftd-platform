import AFTD.Prelude

/-!
# finite_eight_saturated_seed_certificate

Topic: graphs   Node: 1f98c0544aba

Provenance: helper lemma. Finite witness certificate for the two-private-vertex internal-anchor branch of the triangle-packing campaign, experiment 20589.

For the specified twenty-edge graph on eight vertices, the listed seed is a five-packing, each missing support edge and each outside triangle on a seed edge has a listed six-packing witness, and deleting edges 01 and 23 leaves all triangles covered by edges 24, 26, 34 and 36. All witnesses are checked by finite Boolean predicates.
-/

open scoped Sym2
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def in694seed2_edges : Finset (Sym2 (Fin 9)) := {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(1,6),s(2,3),s(2,4),s(2,5),s(2,6),s(2,7),s(3,4),s(3,5),s(3,6),s(3,7),s(4,5),s(4,7),s(5,6),s(6,7)}

def in694seed2_triangle (t : Fin 9 × Fin 9 × Fin 9) : Finset (Sym2 (Fin 9)) :=
  {s(t.1,t.2.1), s(t.1,t.2.2), s(t.2.1,t.2.2)}

def in694seed2_validN (k : Nat) (Q : List (Fin 9 × Fin 9 × Fin 9)) (E : Finset (Sym2 (Fin 9))) : Bool :=
  (Q.length == k) && Q.all (fun t => decide (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ in694seed2_triangle t ⊆ E)) &&
  Q.all (fun t => Q.all (fun u => decide (t = u ∨ Disjoint (in694seed2_triangle t) (in694seed2_triangle u)))) && decide Q.Nodup

def in694seed2_valid := in694seed2_validN 6

def in694seed2_added_edge (i j : Fin 9) : List (Fin 9 × Fin 9 × Fin 9) :=
  if i = 0 ∧ j = 5 then [(2,6,7),(1,3,6),(0,1,2),(3,4,7),(2,4,5),(0,3,5)] else
  if i = 0 ∧ j = 6 then [(2,6,7),(0,3,4),(2,4,5),(3,5,6),(1,2,3),(0,1,6)] else
  if i = 0 ∧ j = 7 then [(3,5,6),(2,4,5),(1,2,6),(0,1,3),(0,4,7),(2,3,7)] else
  if i = 1 ∧ j = 4 then [(2,6,7),(3,5,6),(2,4,5),(3,4,7),(0,1,4),(1,2,3)] else
  if i = 1 ∧ j = 5 then [(2,6,7),(3,4,7),(0,2,4),(0,1,3),(3,5,6),(1,2,5)] else
  if i = 1 ∧ j = 7 then [(3,6,7),(2,5,6),(3,4,5),(1,2,7),(0,1,3),(0,2,4)] else
  if i = 4 ∧ j = 6 then [(0,3,4),(1,2,6),(2,4,5),(3,5,6),(2,3,7),(4,6,7)] else
  if i = 5 ∧ j = 7 then [(0,3,4),(0,1,2),(1,3,6),(2,6,7),(4,5,7),(2,3,5)] else
  []

def in694seed2_outside_triangle (i j : Fin 9) : List (Fin 9 × Fin 9 × Fin 9) :=
  if i = 0 ∧ j = 1 then [(0,1,8),(3,6,7),(1,2,6),(2,4,7),(0,3,4),(2,3,5)] else
  if i = 0 ∧ j = 2 then [(0,2,8),(0,3,4),(2,4,5),(3,5,6),(1,2,6),(2,3,7)] else
  if i = 0 ∧ j = 3 then [(0,3,8),(1,2,3),(2,4,5),(3,5,6),(2,6,7),(3,4,7)] else
  if i = 0 ∧ j = 4 then [(0,4,8),(0,1,3),(1,2,6),(3,5,6),(2,4,5),(2,3,7)] else
  if i = 1 ∧ j = 2 then [(1,2,8),(1,3,6),(2,6,7),(3,4,7),(2,4,5),(0,2,3)] else
  if i = 1 ∧ j = 3 then [(1,3,8),(1,2,6),(3,5,6),(2,4,5),(0,3,4),(2,3,7)] else
  if i = 1 ∧ j = 6 then [(1,6,8),(0,3,4),(0,1,2),(2,4,5),(3,5,6),(2,6,7)] else
  if i = 2 ∧ j = 3 then [(0,3,4),(0,1,2),(2,4,5),(2,3,8),(2,6,7),(3,5,6)] else
  if i = 2 ∧ j = 4 then [(2,4,8),(0,3,4),(0,1,2),(1,3,6),(2,6,7),(2,3,5)] else
  if i = 2 ∧ j = 5 then [(2,5,8),(3,6,7),(1,2,6),(0,1,3),(3,4,5),(2,4,7)] else
  if i = 2 ∧ j = 6 then [(2,6,8),(3,6,7),(2,4,7),(0,3,4),(0,1,2),(2,3,5)] else
  if i = 2 ∧ j = 7 then [(2,7,8),(3,6,7),(1,2,6),(0,1,3),(0,2,4),(3,4,5)] else
  if i = 3 ∧ j = 4 then [(3,4,8),(2,4,5),(3,5,6),(1,2,6),(2,3,7),(0,1,3)] else
  if i = 3 ∧ j = 5 then [(3,5,8),(2,4,5),(0,3,4),(0,1,2),(1,3,6),(2,6,7)] else
  if i = 3 ∧ j = 6 then [(3,6,8),(2,6,7),(3,4,7),(0,2,4),(0,1,3),(2,3,5)] else
  if i = 3 ∧ j = 7 then [(3,7,8),(2,6,7),(3,5,6),(2,4,5),(0,3,4),(0,1,2)] else
  if i = 4 ∧ j = 5 then [(4,5,8),(0,2,4),(1,3,6),(3,4,7),(2,6,7),(2,3,5)] else
  if i = 4 ∧ j = 7 then [(4,7,8),(2,6,7),(3,5,6),(2,4,5),(0,3,4),(0,1,2)] else
  if i = 5 ∧ j = 6 then [(5,6,8),(2,6,7),(1,3,6),(0,1,2),(2,4,5),(0,3,4)] else
  if i = 6 ∧ j = 7 then [(6,7,8),(1,2,6),(3,5,6),(0,3,4),(2,3,7),(2,4,5)] else
  []


theorem in694seed2_added_edges_certified :
    ∀ i j : Fin 9, i.val < 8 → j.val < 8 → i < j → s(i,j) ∉ in694seed2_edges →
      in694seed2_valid (in694seed2_added_edge i j) (insert s(i,j) in694seed2_edges) = true := by
  decide

theorem in694seed2_outside_triangles_certified :
    ∀ i j : Fin 9, i.val < 8 → j.val < 8 → i < j → s(i,j) ∈ in694seed2_edges →
      in694seed2_valid (in694seed2_outside_triangle i j) (insert s(i,8) (insert s(j,8) in694seed2_edges)) = true := by
  decide


theorem in694seed2_base_packing_certified :
    in694seed2_validN 5 [(0,1,2),(3,4,5),(2,4,7),(3,6,7),(2,5,6)] in694seed2_edges = true := by
  decide

theorem in694seed2_deleted_pair_four_cover_certified :
    ∀ i j k : Fin 9, i < j → j < k → k.val < 8 →
      s(i,j) ∈ in694seed2_edges → s(i,k) ∈ in694seed2_edges → s(j,k) ∈ in694seed2_edges →
      s(i,j) ∈ ({s(0,1),s(2,3),s(2,4),s(2,6),s(3,4),s(3,6)} : Finset (Sym2 (Fin 9))) ∨
      s(i,k) ∈ ({s(0,1),s(2,3),s(2,4),s(2,6),s(3,4),s(3,6)} : Finset (Sym2 (Fin 9))) ∨
      s(j,k) ∈ ({s(0,1),s(2,3),s(2,4),s(2,6),s(3,4),s(3,6)} : Finset (Sym2 (Fin 9))) := by
  decide

theorem finite_eight_saturated_seed_certificate :
  (∀ i j : Fin 9, i.val < 8 → j.val < 8 → i < j → s(i,j) ∉ in694seed2_edges →
      in694seed2_valid (in694seed2_added_edge i j) (insert s(i,j) in694seed2_edges) = true) ∧
  (∀ i j : Fin 9, i.val < 8 → j.val < 8 → i < j → s(i,j) ∈ in694seed2_edges →
      in694seed2_valid (in694seed2_outside_triangle i j) (insert s(i,8) (insert s(j,8) in694seed2_edges)) = true) ∧
  (in694seed2_validN 5 [(0,1,2),(3,4,5),(2,4,7),(3,6,7),(2,5,6)] in694seed2_edges = true) ∧
  (∀ i j k : Fin 9, i < j → j < k → k.val < 8 →
      s(i,j) ∈ in694seed2_edges → s(i,k) ∈ in694seed2_edges → s(j,k) ∈ in694seed2_edges →
      s(i,j) ∈ ({s(0,1),s(2,3),s(2,4),s(2,6),s(3,4),s(3,6)} : Finset (Sym2 (Fin 9))) ∨
      s(i,k) ∈ ({s(0,1),s(2,3),s(2,4),s(2,6),s(3,4),s(3,6)} : Finset (Sym2 (Fin 9))) ∨
      s(j,k) ∈ ({s(0,1),s(2,3),s(2,4),s(2,6),s(3,4),s(3,6)} : Finset (Sym2 (Fin 9)))) := by
  exact ⟨in694seed2_added_edges_certified, in694seed2_outside_triangles_certified, in694seed2_base_packing_certified, in694seed2_deleted_pair_four_cover_certified⟩
