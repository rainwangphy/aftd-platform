import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound

/-!
# op1957_endpoint_residual_nonneighbor_budget

Topic: graphs   Node: 22f5eeff7e03

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Endpoint residual nonneighbor budget.
-/

set_option maxHeartbeats 2000000

theorem op1957_endpoint_residual_nonneighbor_budget
    (k c : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (X Y U D : Finset (Fin (4*k))) (x y : Fin (4*k))
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U) (hUD : Disjoint U D)
    (hxX : x ∈ X) (hyY : y ∈ Y) (hyD : y ∉ D) (hD : D.card=2*k-c)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hnoU : ∀ u ∈ U, ¬ G.Adj y u) (hnoD : ∀ d ∈ D, ¬ G.Adj y d)
    (hdegree : 2*k+2 ≤ (G.neighborFinset y).card) :
    ((X.erase x) \ D).card + U.card + 3 ≤ c := by
  classical
  let W := (X.erase x) \ D
  have hWU : Disjoint W U := Finset.disjoint_of_subset_left
    (by intro v hv; exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp hv).1).2) hXU
  have hyU : y ∉ U := fun h => Finset.disjoint_left.mp hYU hyY h
  have hyX : y ∉ X := fun h => Finset.disjoint_left.mp hXY h hyY
  have hsize : Fintype.card (Fin (4*k)) = D.card+(2*k+c-1)+1 := by
    simp only [Fintype.card_fin]
    omega
  have hd : 2*k+c-1 ≤ (G.neighborFinset y).card+(c-3) := by omega
  have hb := anticomplete_neighbor_defect_bound G D y hyD hnoD (2*k+c-1) (c-3) hsize hd
  have hsub : W ∪ U ⊆ (((Finset.univ \ D).erase y) \ G.neighborFinset y) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvW | hvU
    · have hv' := Finset.mem_sdiff.mp hvW
      have hve := Finset.mem_erase.mp hv'.1
      have hvne : v ≠ y := fun h => hyX (h ▸ hve.2)
      have hnon : ¬ G.Adj y v := by
        intro hadj
        exact hve.1 (hcross v hve.2 y hyY hadj.symm).1
      simp only [Finset.mem_sdiff,Finset.mem_erase,Finset.mem_univ,true_and,
        SimpleGraph.mem_neighborFinset]
      exact ⟨⟨hvne,hv'.2⟩,hnon⟩
    · have hvne : v ≠ y := fun h => hyU (h ▸ hvU)
      have hvD : v ∉ D := fun h => Finset.disjoint_left.mp hUD hvU h
      simp only [Finset.mem_sdiff,Finset.mem_erase,Finset.mem_univ,true_and,
        SimpleGraph.mem_neighborFinset]
      exact ⟨⟨hvne,hvD⟩,hnoU v hvU⟩
  have hh := (Finset.card_le_card hsub).trans hb
  rw [Finset.card_union_of_disjoint hWU] at hh
  dsimp [W] at hh
  omega
