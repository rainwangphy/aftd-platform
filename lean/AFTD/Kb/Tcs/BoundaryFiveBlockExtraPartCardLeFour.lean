import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound

/-!
# boundary_five_block_extra_part_card_le_four

Topic: graphs   Node: 9e7b2d7683e2

Provenance: helper lemma. OP-1957: nonclique four-block forced-bridge route; experiment 37135.

In a four-block boundary graph with five vertices in each selected small block and minimum degree at least 2k+2, every set disjoint from the two selected vertices and anticomplete to both has at most four vertices.
-/

theorem boundary_five_block_extra_part_card_le_four
    (k : ℕ) (hk : 5 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hCD : Disjoint C D) (hBD : Disjoint B D)
    (hA : A.card=5) (hC : C.card=5)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C)
    (U : Finset (Fin (4*k))) (hxU : x ∉ U) (hyU : y ∉ U)
    (hUx : ∀ u ∈ U, ¬ G.Adj x u) (hUy : ∀ u ∈ U, ¬ G.Adj y u) :
    U.card ≤ 4 := by
  classical
  have hxB : x ∉ B := (Finset.disjoint_left.mp hAB) hx
  have hyD : y ∉ D := (Finset.disjoint_left.mp hCD) hy
  have hcardB : Fintype.card (Fin (4*k)) = B.card+(2*k+4)+1 := by
    simp only [Fintype.card_fin]
    omega
  have hcardD : Fintype.card (Fin (4*k)) = D.card+(2*k+4)+1 := by
    simp only [Fintype.card_fin]
    omega
  have hdgx : 2*k+4 ≤ (G.neighborFinset x).card+2 := by have := hdegree x; omega
  have hdgy : 2*k+4 ≤ (G.neighborFinset y).card+2 := by have := hdegree y; omega
  let X := ((Finset.univ \ B).erase x) \ G.neighborFinset x
  let Y := ((Finset.univ \ D).erase y) \ G.neighborFinset y
  have hX : X.card ≤ 2 := anticomplete_neighbor_defect_bound G B x hxB
    (hnoAB x hx) (2*k+4) 2 hcardB hdgx
  have hY : Y.card ≤ 2 := anticomplete_neighbor_defect_bound G D y hyD
    (hnoCD y hy) (2*k+4) 2 hcardD hdgy
  have hsubset : U ⊆ X ∪ Y := by
    intro u hu
    by_cases huB : u ∈ B
    · have huD : u ∉ D := (Finset.disjoint_left.mp hBD) huB
      apply Finset.mem_union_right
      simp only [Y, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ,
        true_and, G.mem_neighborFinset]
      exact ⟨⟨fun h => hyU (h ▸ hu), huD⟩, hUy u hu⟩
    · apply Finset.mem_union_left
      simp only [X, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ,
        true_and, G.mem_neighborFinset]
      exact ⟨⟨fun h => hxU (h ▸ hu), huB⟩, hUx u hu⟩
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le X Y
  omega
