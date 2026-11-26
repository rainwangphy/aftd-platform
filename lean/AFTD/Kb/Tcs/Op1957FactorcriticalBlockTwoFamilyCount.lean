import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957FactorcriticalBlockOddGroupsOutsideBound
import AFTD.Kb.Tcs.Op1957ConnectedBlockTwoFamiliesAtMostOne
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# op1957_factorcritical_block_two_family_count

Topic: graphs   Node: 5c0fa5852e8b

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Factorcritical block two family count.
-/

set_option maxHeartbeats 2000000

theorem op1957_factorcritical_block_two_family_count
    {V I J : Type*} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B R : Finset V)
    (hcrit : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hconn : (G.induce {v | v ∈ B}).Connected)
    (K : Finset I) (T : Finset J) (F : I → Finset V) (Q : J → Finset V)
    (hFsub : ∀ i ∈ K, F i ⊆ B ∩ R) (hQsub : ∀ j ∈ T, Q j ⊆ B ∩ R)
    (hQne : ∀ j ∈ T, (Q j).Nonempty) (hQodd : ∀ j ∈ T, Odd (Q j).card)
    (hFdis : ∀ i ∈ K, ∀ l ∈ K, i ≠ l → Disjoint (F i) (F l))
    (hQdis : ∀ i ∈ T, ∀ l ∈ T, i ≠ l → Disjoint (Q i) (Q l))
    (hFQdis : ∀ i ∈ K, ∀ j ∈ T, Disjoint (F i) (Q j))
    (hFanti : ∀ i ∈ K, ∀ l ∈ K, i ≠ l → ∀ u ∈ F i, ∀ v ∈ F l, ¬ G.Adj u v)
    (hQanti : ∀ i ∈ T, ∀ l ∈ T, i ≠ l → ∀ u ∈ Q i, ∀ v ∈ Q l, ¬ G.Adj u v)
    (hFQanti : ∀ i ∈ K, ∀ j ∈ T, ∀ u ∈ F i, ∀ v ∈ Q j, ¬ G.Adj u v)
    (hcover : K.biUnion F ∪ T.biUnion Q = B ∩ R) :
    ((B ∩ R).card < B.card → T.card+(B ∩ R).card+1 ≤ B.card) ∧
    ((B ∩ R).card = B.card → T.card ≤ 1 ∧
      (K.filter (fun i => (F i).Nonempty)).card+T.card ≤ 1) := by
  classical
  constructor
  · intro hless
    have hdiff : (B \ R).Nonempty := by
      apply Finset.card_pos.mp
      have hh := Finset.card_sdiff_add_card_inter B R
      omega
    obtain ⟨z,hz⟩ := hdiff
    have hzB := (Finset.mem_sdiff.mp hz).1
    have hzR := (Finset.mem_sdiff.mp hz).2
    have hanti : ∀ i ∈ T, ∀ u ∈ Q i, ∀ v ∈ B ∩ R, v ∉ Q i → ¬ G.Adj u v := by
      intro i hi u hu v hv hvQ hadj
      have hv' : v ∈ K.biUnion F ∪ T.biUnion Q := by rw [hcover]; exact hv
      rcases Finset.mem_union.mp hv' with hvF | hvUnionQ
      · obtain ⟨l,hl,hvl⟩ := Finset.mem_biUnion.mp hvF
        exact hFQanti l hl i hi v hvl u hu hadj.symm
      · obtain ⟨l,hl,hvl⟩ := Finset.mem_biUnion.mp hvUnionQ
        have hil : i ≠ l := fun h => hvQ (h.symm ▸ hvl)
        exact hQanti i hi l hl hil u hu v hvl hadj
    have hh := op1957_factorcritical_block_odd_groups_outside_bound G B R hcrit T Q
      hQsub hQodd hQdis hanti z hzB hzR
    have hc := Finset.card_sdiff_add_card_inter B R
    omega
  · intro heq
    have hBR : B ∩ R = B := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      omega
    have hcov : K.biUnion F ∪ T.biUnion Q = B := by rw [hcover,hBR]
    have hFs : ∀ i ∈ K, F i ⊆ B := by
      intro i hi v hv
      exact (Finset.mem_inter.mp (hFsub i hi hv)).1
    have hQs : ∀ i ∈ T, Q i ⊆ B := by
      intro i hi v hv
      exact (Finset.mem_inter.mp (hQsub i hi hv)).1
    have hh := op1957_connected_block_two_families_at_most_one G B hconn K T F Q
      hFs hQs hQne hFdis hQdis hFQdis hFanti hQanti hFQanti hcov
    exact ⟨by omega,hh⟩
