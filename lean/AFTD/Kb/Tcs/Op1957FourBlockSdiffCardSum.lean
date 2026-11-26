import AFTD.Prelude

/-!
# op1957_four_block_sdiff_card_sum

Topic: graphs   Node: 95f144d48aaa

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Four block sdiff card sum.
-/

set_option maxHeartbeats 2000000

theorem op1957_four_block_sdiff_card_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Fin 4 → Finset V) (W : Finset V) (forbidden : Fin 4)
    (hdis : ∀ i j : Fin 4, i ≠ j → Disjoint (B i) (B j))
    (hcover : (Finset.univ : Finset (Fin 4)).biUnion B = Finset.univ) :
    (W \ B forbidden).card = ∑ t ∈ (Finset.univ : Finset (Fin 4)).erase forbidden,
      (W ∩ B t).card := by
  classical
  let J : Finset (Fin 4) := Finset.univ.erase forbidden
  have hp : (J : Set (Fin 4)).PairwiseDisjoint (fun t => W ∩ B t) := by
    intro i _ j _ hij
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (hdis i j hij))
  have heq : W \ B forbidden = J.biUnion (fun t => W ∩ B t) := by
    ext v
    constructor
    · intro hv
      have hvW := (Finset.mem_sdiff.mp hv).1
      have hvN := (Finset.mem_sdiff.mp hv).2
      have hvAll : v ∈ (Finset.univ : Finset (Fin 4)).biUnion B := by rw [hcover]; simp
      obtain ⟨i,_,hvi⟩ := Finset.mem_biUnion.mp hvAll
      have hif : i ≠ forbidden := fun h => hvN (h ▸ hvi)
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_erase.mpr ⟨hif,Finset.mem_univ _⟩,
        Finset.mem_inter.mpr ⟨hvW,hvi⟩⟩
    · intro hv
      obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hv
      have hi' := Finset.mem_erase.mp hi
      have hvW := (Finset.mem_inter.mp hvi).1
      have hviB := (Finset.mem_inter.mp hvi).2
      refine Finset.mem_sdiff.mpr ⟨hvW,?_⟩
      intro hvf
      exact Finset.disjoint_left.mp (hdis i forbidden hi'.1) hviB hvf
  rw [heq, Finset.card_biUnion hp]
