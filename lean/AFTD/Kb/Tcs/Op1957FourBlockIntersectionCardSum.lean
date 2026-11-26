import AFTD.Prelude

/-!
# op1957_four_block_intersection_card_sum

Topic: graphs   Node: 67d8327c2972

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Four block intersection card sum.
-/

set_option maxHeartbeats 2000000

theorem op1957_four_block_intersection_card_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Fin 4 → Finset V) (W : Finset V)
    (hBdis : ∀ i j : Fin 4, i ≠ j → Disjoint (B i) (B j))
    (hBcover : (Finset.univ : Finset (Fin 4)).biUnion B = Finset.univ) :
    (∑ b : Fin 4, (W ∩ B b).card) = W.card := by
  classical
  have hp : ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint (fun b => W ∩ B b) := by
    intro i _ j _ hij
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (hBdis i j hij))
  have heq : (Finset.univ : Finset (Fin 4)).biUnion (fun b => W ∩ B b) = W := by
    ext v
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_inter]
    constructor
    · rintro ⟨b,hv,_⟩
      exact hv
    · intro hv
      have hh : v ∈ (Finset.univ : Finset (Fin 4)).biUnion B := by rw [hBcover]; simp
      obtain ⟨b,_,hvb⟩ := Finset.mem_biUnion.mp hh
      exact ⟨b,hv,hvb⟩
  rw [← Finset.card_biUnion hp,heq]
