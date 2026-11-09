import AFTD.Prelude

/-!
# finite_maximal_packing_two_triangle_swap_counterexample

Topic: graphs   Node: cafb859e4e6f

Provenance: helper lemma. Counterexample to the literal replacement in Reduction Rule 8 of https://arxiv.org/html/2308.16515, Section 4.2; this does not refute the paper’s kernel-size theorem.

A finite graph has a maximal packing of three edge-disjoint triangles A, B, C and two edge-disjoint triangles X, Y contained in the vertices of A and B together with vertices outside the packing, such that X and Y cover more vertices than A and B but X shares an edge with C. The graph also has the displayed three-edge triangle cover.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def swapEdges604 : List (Fin 7 × Fin 7) :=
  [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,5),(1,6),
   (2,4),(3,4),(3,5),(3,6)]
def swapGraph604 : SimpleGraph (Fin 7) where
  Adj x y := x ≠ y ∧ ((x,y) ∈ swapEdges604 ∨ (y,x) ∈ swapEdges604)
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩
instance : DecidableRel swapGraph604.Adj := fun x y => inferInstanceAs (Decidable (x ≠ y ∧ _))

theorem swap_maximal604 : ∀ a b c : Fin 7,
    swapGraph604.Adj a b → swapGraph604.Adj a c → swapGraph604.Adj b c →
    2 ≤ (({0,1,2} : Finset (Fin 7)) ∩ {a,b,c}).card ∨
    2 ≤ (({0,3,4} : Finset (Fin 7)) ∩ {a,b,c}).card ∨
    2 ≤ (({1,3,5} : Finset (Fin 7)) ∩ {a,b,c}).card := by
  decide

theorem swap_facts604 :
    swapGraph604.IsNClique 3 ({0,1,2} : Finset (Fin 7)) ∧
    swapGraph604.IsNClique 3 ({0,3,4} : Finset (Fin 7)) ∧
    swapGraph604.IsNClique 3 ({1,3,5} : Finset (Fin 7)) ∧
    (({0,1,2} : Finset (Fin 7)) ∩ {0,3,4}).card ≤ 1 ∧
    (({0,1,2} : Finset (Fin 7)) ∩ {1,3,5}).card ≤ 1 ∧
    (({0,3,4} : Finset (Fin 7)) ∩ {1,3,5}).card ≤ 1 ∧
    swapGraph604.IsNClique 3 ({1,3,6} : Finset (Fin 7)) ∧
    swapGraph604.IsNClique 3 ({0,2,4} : Finset (Fin 7)) ∧
    (({1,3,6} : Finset (Fin 7)) ∩ {0,2,4}).card ≤ 1 ∧
    (({1,3,6} : Finset (Fin 7)) ⊆
      (Finset.univ \ (({0,1,2} : Finset (Fin 7)) ∪ {0,3,4} ∪ {1,3,5})) ∪ {0,1,2} ∪ {0,3,4}) ∧
    (({0,2,4} : Finset (Fin 7)) ⊆
      (Finset.univ \ (({0,1,2} : Finset (Fin 7)) ∪ {0,3,4} ∪ {1,3,5})) ∪ {0,1,2} ∪ {0,3,4}) ∧
    (({0,1,2} : Finset (Fin 7)) ∪ {0,3,4}).card <
      (({1,3,6} : Finset (Fin 7)) ∪ {0,2,4}).card ∧
    2 ≤ (({1,3,6} : Finset (Fin 7)) ∩ {1,3,5}).card := by
  decide

theorem swap_cover604 : ∀ a b c : Fin 7,
    swapGraph604.Adj a b → swapGraph604.Adj a c → swapGraph604.Adj b c →
    ((0 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7)) ∧ (1 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7))) ∨
    ((0 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7)) ∧ (4 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7))) ∨
    ((1 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7)) ∧ (3 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7))) := by
  decide

theorem finite_maximal_packing_two_triangle_swap_counterexample :
    ∃ (G : SimpleGraph (Fin 7)) (A B C X Y : Finset (Fin 7)),
      G.IsNClique 3 A ∧ G.IsNClique 3 B ∧ G.IsNClique 3 C ∧
      (A ∩ B).card ≤ 1 ∧ (A ∩ C).card ≤ 1 ∧ (B ∩ C).card ≤ 1 ∧
      G.IsNClique 3 X ∧ G.IsNClique 3 Y ∧ (X ∩ Y).card ≤ 1 ∧
      X ⊆ (Finset.univ \ (A ∪ B ∪ C)) ∪ A ∪ B ∧
      Y ⊆ (Finset.univ \ (A ∪ B ∪ C)) ∪ A ∪ B ∧
      (A ∪ B).card < (X ∪ Y).card ∧ 2 ≤ (X ∩ C).card ∧
      (∀ t : Finset (Fin 7), G.IsNClique 3 t →
        2 ≤ (A ∩ t).card ∨ 2 ≤ (B ∩ t).card ∨ 2 ≤ (C ∩ t).card) ∧
      (∀ a b c : Fin 7, G.Adj a b → G.Adj a c → G.Adj b c →
        ((0 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7)) ∧ (1 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7))) ∨
        ((0 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7)) ∧ (4 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7))) ∨
        ((1 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7)) ∧ (3 : Fin 7) ∈ ({a,b,c} : Finset (Fin 7)))) := by
  refine ⟨swapGraph604, {0,1,2}, {0,3,4}, {1,3,5}, {1,3,6}, {0,2,4}, ?_⟩
  rcases swap_facts604 with ⟨hA,hB,hC,hAB,hAC,hBC,hX,hY,hXY,hsubX,hsubY,hmore,hconf⟩
  refine ⟨hA,hB,hC,hAB,hAC,hBC,hX,hY,hXY,hsubX,hsubY,hmore,hconf, ?_, swap_cover604⟩
  intro t ht
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  exact swap_maximal604 a b c
    (ht.isClique (by simp) (by simp) hab)
    (ht.isClique (by simp) (by simp) hac)
    (ht.isClique (by simp) (by simp) hbc)
