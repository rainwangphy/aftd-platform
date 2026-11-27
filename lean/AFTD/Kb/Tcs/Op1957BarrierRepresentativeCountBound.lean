import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteVertexFourDisjointNonneighborSetsBound
import AFTD.Kb.Tcs.PairwiseDisjointNonemptyGroupsCardBound

/-!
# op1957_barrier_representative_count_bound

Topic: graphs   Node: dca7450a8b39

Provenance: helper lemma. OP-1957: one-defect boundary graph-to-count transfer, arXiv:2611.22690

A representative in a disjoint anticomplete barrier group yields the displayed bound on endpoint-shore vertices outside a forbidden block and the number of barrier groups, with a correction for pool vertices inside the block.
-/

theorem op1957_barrier_representative_count_bound
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Q X Y : Finset V)
    (K : Finset I) (T : I → Finset V) (j : I) (hj : j ∈ K)
    (hne : ∀ i ∈ K, (T i).Nonempty)
    (hTT : ∀ i ∈ K, ∀ l ∈ K, i ≠ l → Disjoint (T i) (T l))
    (hXY : Disjoint X Y) (hXT : ∀ i ∈ K, Disjoint X (T i))
    (hYT : ∀ i ∈ K, Disjoint Y (T i))
    (q : V) (hq : q ∈ T j) (hqQ : q ∉ Q)
    (hQ : ∀ z ∈ Q, ¬ G.Adj q z)
    (hX : ∀ z ∈ X, ¬ G.Adj q z) (hY : ∀ z ∈ Y, ¬ G.Adj q z)
    (hT : ∀ i ∈ K, i ≠ j → ∀ z ∈ T i, ¬ G.Adj q z)
    (d r : ℕ) (hsize : Fintype.card V = Q.card+d+1)
    (hdegree : d ≤ (G.neighborFinset q).card+r) :
    let U := K.biUnion T
    (X \ Q).card+(Y \ Q).card+K.card ≤ r+1+(U ∩ Q).card := by
  classical
  let U := K.biUnion T
  let W := U \ T j
  have hjU : T j ⊆ U := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨j,hj,hz⟩
  have hWsub : W ⊆ U := Finset.sdiff_subset
  have hWcard : K.card ≤ W.card+1 := by
    have hh := pairwise_disjoint_nonempty_groups_card_bound K T j hj hTT hne
    have hc := Finset.card_sdiff_add_card_eq_card hjU
    change (T j).card+K.card ≤ U.card+1 at hh
    change W.card+(T j).card=U.card at hc
    omega
  have hXU : Disjoint X U := (Finset.disjoint_biUnion_right X K T).mpr hXT
  have hYU : Disjoint Y U := (Finset.disjoint_biUnion_right Y K T).mpr hYT
  have hXW : Disjoint X W := Finset.disjoint_of_subset_right hWsub hXU
  have hYW : Disjoint Y W := Finset.disjoint_of_subset_right hWsub hYU
  have hqX : q ∉ X := fun h => Finset.disjoint_left.mp (hXT j hj) h hq
  have hqY : q ∉ Y := fun h => Finset.disjoint_left.mp (hYT j hj) h hq
  have hqW : q ∉ W := by simp [W,hq]
  have hWanti : ∀ z ∈ W, ¬ G.Adj q z := by
    intro z hz
    have hzU := (Finset.mem_sdiff.mp hz).1
    have hzT := (Finset.mem_sdiff.mp hz).2
    obtain ⟨i,hi,hzi⟩ := Finset.mem_biUnion.mp hzU
    have hij : i ≠ j := by intro he; subst i; exact hzT hzi
    exact hT i hi hij z hzi
  have hs : ∀ z, (z ∈ X ∨ z ∈ Y ∨ z ∈ W ∨ z ∈ (∅ : Finset V)) → z ≠ q ∧ ¬ G.Adj q z := by
    intro z hz
    rcases hz with hz | hz | hz | hz
    · exact ⟨fun he => hqX (he ▸ hz),hX z hz⟩
    · exact ⟨fun he => hqY (he ▸ hz),hY z hz⟩
    · exact ⟨fun he => hqW (he ▸ hz),hWanti z hz⟩
    · simp at hz
  have hbudget := anticomplete_vertex_four_disjoint_nonneighbor_sets_bound G Q q hqQ hQ d r hsize hdegree
    X Y W ∅ hs hXY hXW (by simp) hYW (by simp) (by simp)
  simp only [Finset.empty_sdiff,Finset.card_empty,add_zero] at hbudget
  have hsplit := Finset.card_inter_add_card_sdiff W Q
  have hcap : (W ∩ Q).card ≤ (U ∩ Q).card := by
    apply Finset.card_le_card
    intro z hz
    exact Finset.mem_inter.mpr ⟨hWsub (Finset.mem_inter.mp hz).1,(Finset.mem_inter.mp hz).2⟩
  change (X \ Q).card+(Y \ Q).card+K.card ≤ r+1+(U ∩ Q).card
  omega
