import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteMaximalPackingTwoTriangleSwapCounterexample

/-!
# finite_packing_swap_no_valid_replacement_after_preprocessing

Topic: graphs   Node: dbcae5243656

Provenance: helper lemma. The replacement condition in Reduction Rule 8 of https://arxiv.org/html/2308.16515, Section 4.2, and its conference version; no claim is made about the kernel theorem or the later journal version.

In the seven-vertex maximum-packing example, none of the three pairs of packed triangles admits a valid two-triangle replacement with greater vertex support, although the stated rule has a candidate that conflicts with the untouched third triangle. Every vertex and edge is triangle-active, each neighborhood is connected, and there is no four-clique.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def swapAllTriangles604 : Finset (Finset (Fin 7)) :=
  {{0,1,2}, {0,1,3}, {0,2,4}, {0,3,4}, {1,3,5}, {1,3,6}}

def swapImproves604 (A B C X Y : Finset (Fin 7)) : Prop :=
  X ⊆ (Finset.univ \ (A ∪ B ∪ C)) ∪ A ∪ B ∧
  Y ⊆ (Finset.univ \ (A ∪ B ∪ C)) ∪ A ∪ B ∧
  (A ∪ B).card < (X ∪ Y).card ∧
  (X ∩ Y).card ≤ 1 ∧ (X ∩ C).card ≤ 1 ∧ (Y ∩ C).card ≤ 1

instance (A B C X Y : Finset (Fin 7)) : Decidable (swapImproves604 A B C X Y) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem swap_triangle_table604 : ∀ a b c : Fin 7,
    swapGraph604.Adj a b → swapGraph604.Adj a c → swapGraph604.Adj b c →
      ({a,b,c} : Finset (Fin 7)) ∈ swapAllTriangles604 := by
  decide

theorem swap_triangle_list604 (t : Finset (Fin 7)) (ht : swapGraph604.IsNClique 3 t) :
    t ∈ swapAllTriangles604 := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  exact swap_triangle_table604 a b c
    (ht.isClique (by simp) (by simp) hab)
    (ht.isClique (by simp) (by simp) hac)
    (ht.isClique (by simp) (by simp) hbc)

theorem swap_no_valid_replacement_table604 :
    ∀ X ∈ swapAllTriangles604, ∀ Y ∈ swapAllTriangles604,
      ¬ swapImproves604 {0,1,2} {0,3,4} {1,3,5} X Y ∧
      ¬ swapImproves604 {0,1,2} {1,3,5} {0,3,4} X Y ∧
      ¬ swapImproves604 {0,3,4} {1,3,5} {0,1,2} X Y := by
  decide

theorem swap_no_valid_replacement604 (X Y : Finset (Fin 7))
    (hX : swapGraph604.IsNClique 3 X) (hY : swapGraph604.IsNClique 3 Y) :
      ¬ swapImproves604 {0,1,2} {0,3,4} {1,3,5} X Y ∧
      ¬ swapImproves604 {0,1,2} {1,3,5} {0,3,4} X Y ∧
      ¬ swapImproves604 {0,3,4} {1,3,5} {0,1,2} X Y :=
  swap_no_valid_replacement_table604 X (swap_triangle_list604 X hX) Y (swap_triangle_list604 Y hY)

theorem swap_all_edges_active604 : ∀ u v : Fin 7,
    swapGraph604.Adj u v → ∃ w : Fin 7, swapGraph604.Adj u w ∧ swapGraph604.Adj v w := by
  decide

theorem swap_all_vertices_active604 : ∀ u : Fin 7, ∃ v : Fin 7, swapGraph604.Adj u v := by
  decide

theorem swap_neighborhood_diameter_three604 : ∀ u v w : Fin 7,
    swapGraph604.Adj u v → swapGraph604.Adj u w →
      v = w ∨ swapGraph604.Adj v w ∨
      (∃ z : Fin 7, swapGraph604.Adj u z ∧ swapGraph604.Adj v z ∧ swapGraph604.Adj z w) ∨
      (∃ z z' : Fin 7, swapGraph604.Adj u z ∧ swapGraph604.Adj u z' ∧
        swapGraph604.Adj v z ∧ swapGraph604.Adj z z' ∧ swapGraph604.Adj z' w) := by
  decide

theorem swap_no_four_clique604 : ∀ t : Finset (Fin 7), ¬ swapGraph604.IsNClique 4 t := by
  decide

theorem finite_packing_swap_no_valid_replacement_after_preprocessing :
  (∀ X Y : Finset (Fin 7), swapGraph604.IsNClique 3 X → swapGraph604.IsNClique 3 Y →
      ¬ swapImproves604 {0,1,2} {0,3,4} {1,3,5} X Y ∧
      ¬ swapImproves604 {0,1,2} {1,3,5} {0,3,4} X Y ∧
      ¬ swapImproves604 {0,3,4} {1,3,5} {0,1,2} X Y) ∧
  (∀ u v : Fin 7, swapGraph604.Adj u v → ∃ w : Fin 7, swapGraph604.Adj u w ∧ swapGraph604.Adj v w) ∧
  (∀ u : Fin 7, ∃ v : Fin 7, swapGraph604.Adj u v) ∧
  (∀ u v w : Fin 7, swapGraph604.Adj u v → swapGraph604.Adj u w →
      v = w ∨ swapGraph604.Adj v w ∨
      (∃ z : Fin 7, swapGraph604.Adj u z ∧ swapGraph604.Adj v z ∧ swapGraph604.Adj z w) ∨
      (∃ z z' : Fin 7, swapGraph604.Adj u z ∧ swapGraph604.Adj u z' ∧
        swapGraph604.Adj v z ∧ swapGraph604.Adj z z' ∧ swapGraph604.Adj z' w)) ∧
  (∀ t : Finset (Fin 7), ¬ swapGraph604.IsNClique 4 t) := by
  exact ⟨swap_no_valid_replacement604, swap_all_edges_active604,
    swap_all_vertices_active604, swap_neighborhood_diameter_three604, swap_no_four_clique604⟩
