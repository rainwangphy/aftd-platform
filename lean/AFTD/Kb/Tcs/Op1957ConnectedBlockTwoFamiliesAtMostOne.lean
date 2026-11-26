import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957ConnectedBlockAnticompleteGroupsAtMostOne

/-!
# op1957_connected_block_two_families_at_most_one

Topic: graphs   Node: 78cff90fc28b

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Connected block two families at most one.
-/

set_option maxHeartbeats 2000000

theorem op1957_connected_block_two_families_at_most_one
    {V I J : Type*} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]
    (G : SimpleGraph V) (B : Finset V) (hconn : (G.induce {v | v ∈ B}).Connected)
    (K : Finset I) (T : Finset J) (F : I → Finset V) (Q : J → Finset V)
    (hFsub : ∀ i ∈ K, F i ⊆ B) (hQsub : ∀ j ∈ T, Q j ⊆ B)
    (hQne : ∀ j ∈ T, (Q j).Nonempty)
    (hFdis : ∀ i ∈ K, ∀ l ∈ K, i ≠ l → Disjoint (F i) (F l))
    (hQdis : ∀ i ∈ T, ∀ l ∈ T, i ≠ l → Disjoint (Q i) (Q l))
    (hFQdis : ∀ i ∈ K, ∀ j ∈ T, Disjoint (F i) (Q j))
    (hFanti : ∀ i ∈ K, ∀ l ∈ K, i ≠ l → ∀ u ∈ F i, ∀ v ∈ F l, ¬ G.Adj u v)
    (hQanti : ∀ i ∈ T, ∀ l ∈ T, i ≠ l → ∀ u ∈ Q i, ∀ v ∈ Q l, ¬ G.Adj u v)
    (hFQanti : ∀ i ∈ K, ∀ j ∈ T, ∀ u ∈ F i, ∀ v ∈ Q j, ¬ G.Adj u v)
    (hcover : K.biUnion F ∪ T.biUnion Q = B) :
    (K.filter (fun i => (F i).Nonempty)).card+T.card ≤ 1 := by
  classical
  let K' := K.filter (fun i => (F i).Nonempty)
  let M : Finset (I ⊕ J) := K'.disjSum T
  let H : I ⊕ J → Finset V := Sum.elim F Q
  have hsub : ∀ i ∈ M, H i ⊆ B := by
    intro i hi
    cases i with
    | inl i =>
      have hi' : i ∈ K' := by simpa [M] using hi
      exact hFsub i (Finset.mem_filter.mp hi').1
    | inr i =>
      have hi' : i ∈ T := by simpa [M] using hi
      exact hQsub i hi'
  have hne : ∀ i ∈ M, (H i).Nonempty := by
    intro i hi
    cases i with
    | inl i =>
      have hi' : i ∈ K' := by simpa [M] using hi
      exact (Finset.mem_filter.mp hi').2
    | inr i =>
      have hi' : i ∈ T := by simpa [M] using hi
      exact hQne i hi'
  have hdis : ∀ i ∈ M, ∀ j ∈ M, i ≠ j → Disjoint (H i) (H j) := by
    intro i hi j hj hij
    cases i with
    | inl i =>
      have hi' : i ∈ K := by
        have hh : i ∈ K' := by simpa [M] using hi
        exact (Finset.mem_filter.mp hh).1
      cases j with
      | inl j =>
        have hj' : j ∈ K := by
          have hh : j ∈ K' := by simpa [M] using hj
          exact (Finset.mem_filter.mp hh).1
        exact hFdis i hi' j hj' (fun h => hij (by simp [h]))
      | inr j =>
        have hj' : j ∈ T := by simpa [M] using hj
        exact hFQdis i hi' j hj'
    | inr i =>
      have hi' : i ∈ T := by simpa [M] using hi
      cases j with
      | inl j =>
        have hj' : j ∈ K := by
          have hh : j ∈ K' := by simpa [M] using hj
          exact (Finset.mem_filter.mp hh).1
        exact (hFQdis j hj' i hi').symm
      | inr j =>
        have hj' : j ∈ T := by simpa [M] using hj
        exact hQdis i hi' j hj' (fun h => hij (by simp [h]))
  have hanti : ∀ i ∈ M, ∀ j ∈ M, i ≠ j → ∀ u ∈ H i, ∀ v ∈ H j, ¬ G.Adj u v := by
    intro i hi j hj hij u hu v hv hadj
    cases i with
    | inl i =>
      have hi' : i ∈ K := by
        have hh : i ∈ K' := by simpa [M] using hi
        exact (Finset.mem_filter.mp hh).1
      cases j with
      | inl j =>
        have hj' : j ∈ K := by
          have hh : j ∈ K' := by simpa [M] using hj
          exact (Finset.mem_filter.mp hh).1
        exact hFanti i hi' j hj' (fun h => hij (by simp [h])) u hu v hv hadj
      | inr j =>
        have hj' : j ∈ T := by simpa [M] using hj
        exact hFQanti i hi' j hj' u hu v hv hadj
    | inr i =>
      have hi' : i ∈ T := by simpa [M] using hi
      cases j with
      | inl j =>
        have hj' : j ∈ K := by
          have hh : j ∈ K' := by simpa [M] using hj
          exact (Finset.mem_filter.mp hh).1
        exact hFQanti j hj' i hi' v hv u hu hadj.symm
      | inr j =>
        have hj' : j ∈ T := by simpa [M] using hj
        exact hQanti i hi' j hj' (fun h => hij (by simp [h])) u hu v hv hadj
  have hMcover : M.biUnion H = B := by
    ext v
    constructor
    · intro hv
      obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hv
      exact hsub i hi hvi
    · intro hv
      have hv' : v ∈ K.biUnion F ∪ T.biUnion Q := by rw [hcover]; exact hv
      rcases Finset.mem_union.mp hv' with hvF | hvQ
      · obtain ⟨i,hi,hvi⟩ := Finset.mem_biUnion.mp hvF
        have hi' : i ∈ K' := Finset.mem_filter.mpr ⟨hi,⟨v,hvi⟩⟩
        exact Finset.mem_biUnion.mpr ⟨Sum.inl i,by simpa [M] using hi',hvi⟩
      · obtain ⟨j,hj,hvj⟩ := Finset.mem_biUnion.mp hvQ
        exact Finset.mem_biUnion.mpr ⟨Sum.inr j,by simpa [M] using hj,hvj⟩
  have hh := op1957_connected_block_anticomplete_groups_at_most_one G B hconn M H hsub hne hdis hanti hMcover
  simpa [M,K',Finset.card_disjSum] using hh
