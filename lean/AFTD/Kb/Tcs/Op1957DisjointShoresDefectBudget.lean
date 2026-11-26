import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound

/-!
# op1957_disjoint_shores_defect_budget

Topic: graphs   Node: bd34d003347d

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Disjoint shores defect budget.
-/

set_option maxHeartbeats 2000000

theorem op1957_disjoint_shores_defect_budget
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Finset I) (F : I → Finset V) (E T : Finset V) (j : I) (v : V)
    (hj : j ∈ J) (hv : v ∈ F j)
    (hdis : ∀ i ∈ J, ∀ l ∈ J, i ≠ l → Disjoint (F i) (F l))
    (hdisE : ∀ i ∈ J, Disjoint (F i) E)
    (hanti : ∀ i ∈ J, i ≠ j → ∀ w ∈ F i, ¬ G.Adj v w)
    (hantiE : ∀ w ∈ E, ¬ G.Adj v w)
    (hvT : v ∉ T) (hforbid : ∀ w ∈ T, ¬ G.Adj v w)
    (d r : ℕ) (hsize : Fintype.card V = T.card+d+1)
    (hdegree : d ≤ (G.neighborFinset v).card+r) :
    (∑ i ∈ J.erase j, (F i \ T).card) + (E \ T).card ≤ r := by
  classical
  let J' := J.erase j
  let H : I → Finset V := fun i => F i \ T
  let E' := E \ T
  have hp : (J' : Set I).PairwiseDisjoint H := by
    intro i hi l hl hil
    have hi' := Finset.mem_erase.mp hi
    have hl' := Finset.mem_erase.mp hl
    exact Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset (hdis i hi'.2 l hl'.2 hil))
  have he : Disjoint (J'.biUnion H) E' := by
    apply Finset.disjoint_left.mpr
    intro w hw hwE
    obtain ⟨i,hi,hwi⟩ := Finset.mem_biUnion.mp hw
    have hiJ := (Finset.mem_erase.mp hi).2
    exact Finset.disjoint_left.mp (hdisE i hiJ) (Finset.mem_sdiff.mp hwi).1 (Finset.mem_sdiff.mp hwE).1
  have hsubset : J'.biUnion H ∪ E' ⊆ (((Finset.univ \ T).erase v) \ G.neighborFinset v) := by
    intro w hw
    have hwv : w ≠ v := by
      intro h
      subst w
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hw
        have hi' := Finset.mem_erase.mp hi
        exact Finset.disjoint_left.mp (hdis j hj i hi'.2 (Ne.symm hi'.1)) hv (Finset.mem_sdiff.mp hvi).1
      · exact Finset.disjoint_left.mp (hdisE j hj) hv (Finset.mem_sdiff.mp hw).1
    have hwT : w ∉ T := by
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨i,_,hwi⟩ := Finset.mem_biUnion.mp hw
        exact (Finset.mem_sdiff.mp hwi).2
      · exact (Finset.mem_sdiff.mp hw).2
    have hnon : ¬ G.Adj v w := by
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨i,hi,hwi⟩ := Finset.mem_biUnion.mp hw
        have hi' := Finset.mem_erase.mp hi
        exact hanti i hi'.2 hi'.1 w (Finset.mem_sdiff.mp hwi).1
      · exact hantiE w (Finset.mem_sdiff.mp hw).1
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hwv,hwT⟩,hnon⟩
  have hb := anticomplete_neighbor_defect_bound G T v hvT hforbid d r hsize hdegree
  have hc := (Finset.card_le_card hsubset).trans hb
  rw [Finset.card_union_of_disjoint he, Finset.card_biUnion hp] at hc
  simpa [J',H,E'] using hc
