import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957ConnectedAnticompletePartitionCard

/-!
# op1957_connected_block_anticomplete_groups_at_most_one

Topic: graphs   Node: f5d1e57a4e80

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Connected block anticomplete groups at most one.
-/

set_option maxHeartbeats 2000000

theorem op1957_connected_block_anticomplete_groups_at_most_one
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (B : Finset V)
    (hconn : (G.induce {v | v ∈ B}).Connected)
    (J : Finset I) (F : I → Finset V)
    (hsub : ∀ i ∈ J, F i ⊆ B)
    (hne : ∀ i ∈ J, (F i).Nonempty)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j))
    (hanti : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ u ∈ F i, ∀ v ∈ F j, ¬ G.Adj u v)
    (hcover : J.biUnion F = B) : J.card ≤ 1 := by
  classical
  let H := G.induce {v | v ∈ B}
  let Q : I → Finset {v // v ∈ B} := fun i => (F i).subtype (· ∈ B)
  have hQne : ∀ i ∈ J, (Q i).Nonempty := by
    intro i hi
    obtain ⟨u,hu⟩ := hne i hi
    refine ⟨⟨u,hsub i hi hu⟩,?_⟩
    simpa [Q] using hu
  have hQdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (Q i) (Q j) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro u hui huj
    have hui' : u.val ∈ F i := by simpa [Q] using hui
    have huj' : u.val ∈ F j := by simpa [Q] using huj
    exact Finset.disjoint_left.mp (hdis i hi j hj hij) hui' huj'
  have hQanti : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ u ∈ Q i, ∀ v ∈ Q j, ¬ H.Adj u v := by
    intro i hi j hj hij u hu v hv hadj
    have hu' : u.val ∈ F i := by simpa [Q] using hu
    have hv' : v.val ∈ F j := by simpa [Q] using hv
    exact hanti i hi j hj hij u.val hu' v.val hv' hadj
  have hQcover : J.biUnion Q = Finset.univ := by
    ext v
    simp only [Finset.mem_univ,iff_true]
    have hv : v.val ∈ J.biUnion F := by rw [hcover]; exact v.property
    obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨i,hi,by simpa [Q] using hvi⟩
  exact op1957_connected_anticomplete_partition_card H hconn J Q hQne hQdis hQanti hQcover
