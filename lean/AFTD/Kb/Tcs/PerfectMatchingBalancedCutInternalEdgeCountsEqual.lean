import AFTD.Prelude
import AFTD.Kb.Tcs.PerfectMatchingInternalEdgeCard

/-!
# perfect_matching_balanced_cut_internal_edge_counts_equal

Topic: graphs   Node: a59de9772045

Provenance: helper lemma. Balanced-cut structural reduction for OP-1957; https://arxiv.org/abs/2611.22690.

A perfect matching has equally many internal edges on each side of a balanced partition.
-/

theorem perfect_matching_balanced_cut_internal_edge_counts_equal
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (C : Finset V) (hcard : 2*C.card = Fintype.card V) :
    (P.induce (C : Set V)).edgeSet.ncard =
      (P.induce ((C : Set V)ᶜ)).edgeSet.ncard := by
  set_option maxHeartbeats 4000000 in
    classical
    let f : V → V := fun v => (hP.1 (hP.2 v)).choose
    have hf : ∀ v, P.Adj v (f v) := by
      intro v
      exact (hP.1 (hP.2 v)).choose_spec.1
    have hinv : Function.Involutive f := by
      intro v
      exact (hP.1 (hP.2 (f v))).unique (hf (f v)) (hf v).symm
    have hcross : (C.filter (fun v => f v ∉ C)).card =
        ((Cᶜ : Finset V).filter (fun v => f v ∈ C)).card := by
      apply Finset.card_bij' (fun v _ => f v) (fun v _ => f v)
      · intro v hv
        simp only [Finset.mem_filter,Finset.mem_compl] at hv ⊢
        exact ⟨hv.2,by rw [hinv]; exact hv.1⟩
      · intro v hv
        simp only [Finset.mem_filter,Finset.mem_compl] at hv ⊢
        exact ⟨hv.2,by rw [hinv]; exact hv.1⟩
      · intro v hv
        exact hinv v
      · intro v hv
        exact hinv v
    have h1 := perfect_matching_internal_edge_card G P hP f hf C
    have h2 := perfect_matching_internal_edge_card G P hP f hf (Cᶜ : Finset V)
    have hcomp : ((Cᶜ : Finset V) : Set V) = (C : Set V)ᶜ := by ext v; simp
    rw [hcomp] at h2
    have hsplit1 := Finset.card_filter_add_card_filter_not (s:=C) (fun v => f v ∈ C)
    have hsplit2 := Finset.card_filter_add_card_filter_not (s:=(Cᶜ : Finset V)) (fun v => f v ∈ (Cᶜ : Finset V))
    have hcompcard : (Cᶜ : Finset V).card + C.card = Fintype.card V := by simp
    simp only [Finset.mem_compl,not_not] at hsplit2 h2
    omega
