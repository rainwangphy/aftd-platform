import AFTD.Prelude

/-!
# tree_card_four_degree_two_count

Topic: graphs   Node: af695c00d7c5

Provenance: helper lemma. step towards tree_card_four_iso_of_degree_le_two

In a tree on 4 vertices with all degrees at most 2, exactly two vertices have degree 2 and two vertices have degree 1.
-/

/-- In a tree on 4 vertices with all degrees at most 2, exactly two vertices have degree 2 and two vertices have degree 1. -/
theorem tree_card_four_degree_two_count {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : Fintype.card V = 4)
    (hdeg : ∀ v : V, T.degree v ≤ 2) :
    (Finset.univ.filter (fun v => T.degree v = 2)).card = 2 ∧
    (Finset.univ.filter (fun v => T.degree v = 1)).card = 2 := by
  have h_nontriv : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have h_ne_zero : ∀ v : V, T.degree v ≠ 0 := by
    intro v h0
    have h_iso : ¬ T.IsIsolated v := hT.connected.preconnected.not_isIsolated v
    rw [SimpleGraph.degree_eq_zero] at h0
    exact h_iso h0
  have h_deg_cases : ∀ v : V, T.degree v = 1 ∨ T.degree v = 2 := by
    intro v
    have h1 := hdeg v
    have h2 := h_ne_zero v
    omega
  let S1 := Finset.univ.filter (fun v => T.degree v = 1)
  let S2 := Finset.univ.filter (fun v => T.degree v = 2)
  have hd : Disjoint S1 S2 := by
    rw [Finset.disjoint_filter]
    intro x _ hx1 hx2
    omega
  have hu : S1 ∪ S2 = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, S1, S2]
    exact iff_true_intro (h_deg_cases x)
  have h_card_sum : S1.card + S2.card = 4 := by
    have := Finset.card_union_of_disjoint hd
    rw [hu, Finset.card_univ, hcard] at this
    exact this.symm
  have hs : ∑ v : V, T.degree v = ∑ v ∈ S1 ∪ S2, T.degree v := by
    rw [hu]
  have s1 : ∑ v ∈ S1, T.degree v = S1.card := by
    rw [Finset.sum_const_nat (m := 1), mul_one]
    intro x hx
    simp only [S1, Finset.mem_filter] at hx
    exact hx.2
  have s2 : ∑ v ∈ S2, T.degree v = 2 * S2.card := by
    rw [Finset.sum_const_nat (m := 2), mul_comm]
    intro x hx
    simp only [S2, Finset.mem_filter] at hx
    exact hx.2
  have h_deg_sum : ∑ v : V, T.degree v = S1.card + 2 * S2.card := by
    rw [hs, Finset.sum_union hd, s1, s2]
  have h_edge := hT.card_edgeFinset
  have h_handshake := T.sum_degrees_eq_twice_card_edges
  have h_total : ∑ v : V, T.degree v = 6 := by omega
  have h_s2 : S2.card = 2 := by omega
  have h_s1 : S1.card = 2 := by omega
  exact ⟨h_s2, h_s1⟩
