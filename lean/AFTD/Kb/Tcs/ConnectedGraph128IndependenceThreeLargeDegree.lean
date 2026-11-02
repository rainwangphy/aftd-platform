import AFTD.Prelude

/-!
# connected_graph_128_independence_three_large_degree

Topic: graphs   Node: 174500445d02

Provenance: helper lemma. Elementary closed-neighborhood counting refinement of the auxiliary-graph route for OP-110.

Every connected simple graph on 128 vertices with no independent set of size four has a vertex of degree at least 43.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem connected_graph_128_independence_three_large_degree
    (G : SimpleGraph (Fin 128)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hindep : G.IndepSetFree 4) :
    ∃ v, 43 ≤ G.degree v := by
  classical
  by_contra hbad
  have hdeg : ∀ v, G.degree v ≤ 42 := by
    intro v
    have h := hbad
    push_neg at h
    have hv := h v
    omega
  let N : Fin 128 → Finset (Fin 128) := fun v => insert v (G.neighborFinset v)
  have hN : ∀ v, (N v).card ≤ 43 := by
    intro v
    have hc := Finset.card_insert_le v (G.neighborFinset v)
    have hd := hdeg v
    change (N v).card ≤ (G.neighborFinset v).card + 1 at hc
    change (G.neighborFinset v).card ≤ 42 at hd
    omega
  have hNmem : ∀ x y, y ∈ N x ↔ y = x ∨ G.Adj x y := by
    intro x y
    simp [N, SimpleGraph.mem_neighborFinset]
  have hne : ∃ x : Fin 128, x ∉ N 0 := by
    by_contra h
    push_neg at h
    have he : N 0 = Finset.univ := by
      ext x
      simp [h x]
    have hc := hN 0
    rw [he] at hc
    norm_num at hc
  obtain ⟨x, hx⟩ := hne
  have hxne : (0 : Fin 128) ≠ x := by
    intro h
    subst x
    exact hx ((hNmem 0 0).2 (Or.inl rfl))
  have hxadj : ¬ G.Adj 0 x := by
    intro h
    exact hx ((hNmem 0 x).2 (Or.inr h))
  obtain ⟨p, hp⟩ := (hconn 0 x).exists_path_of_dist
  obtain ⟨a, w, b, haw, hwb, hab, habne⟩ :=
    p.exists_adj_adj_not_adj_ne hp.2 ((hconn 0 x).one_lt_dist_of_ne_of_not_adj hxne hxadj)
  let S := N a ∪ N b
  have hcap : S.card ≤ 85 := by
    have hi : (N a ∩ N b).Nonempty := by
      refine ⟨w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · exact (hNmem a w).2 (Or.inr haw)
      · exact (hNmem b w).2 (Or.inr hwb.symm)
    have hc := Finset.card_union_add_card_inter (N a) (N b)
    have hi' := Finset.card_pos.mpr hi
    have ha := hN a
    have hb := hN b
    change S.card + _ = _ at hc
    omega
  have haS : a ∈ S := Finset.mem_union_left _ ((hNmem a a).2 (Or.inl rfl))
  have hcS : ∀ c ∉ S, Disjoint S (N c) := by
    intro c hc
    have hca : c ≠ a ∧ ¬ G.Adj a c := by
      have hca' : c ∉ N a := by intro h; exact hc (Finset.mem_union_left _ h)
      simpa [hNmem, ne_comm] using hca'
    have hcb : c ≠ b ∧ ¬ G.Adj b c := by
      have hcb' : c ∉ N b := by intro h; exact hc (Finset.mem_union_right _ h)
      simpa [hNmem, ne_comm] using hcb'
    have hcover : S ∪ N c = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro d
      by_contra hd
      have hdS : d ∉ S := fun h => hd (Finset.mem_union_left _ h)
      have hdN : d ∉ N c := fun h => hd (Finset.mem_union_right _ h)
      have hda : d ≠ a ∧ ¬ G.Adj a d := by
        have hda' : d ∉ N a := by intro h; exact hdS (Finset.mem_union_left _ h)
        simpa [hNmem, ne_comm] using hda'
      have hdb : d ≠ b ∧ ¬ G.Adj b d := by
        have hdb' : d ∉ N b := by intro h; exact hdS (Finset.mem_union_right _ h)
        simpa [hNmem, ne_comm] using hdb'
      have hdc : d ≠ c ∧ ¬ G.Adj c d := by
        simpa [hNmem, ne_comm] using hdN
      have hba : ¬ G.Adj b a := fun h => hab h.symm
      have hca' : ¬ G.Adj c a := fun h => hca.2 h.symm
      have hcb' : ¬ G.Adj c b := fun h => hcb.2 h.symm
      have hda' : ¬ G.Adj d a := fun h => hda.2 h.symm
      have hdb' : ¬ G.Adj d b := fun h => hdb.2 h.symm
      have hdc' : ¬ G.Adj d c := fun h => hdc.2 h.symm
      have hfour : G.IsNIndepSet 4 ({a, b, c, d} : Finset (Fin 128)) := by
        constructor
        · intro u hu v hv huv
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hu hv
          rcases hu with rfl | rfl | rfl | rfl <;>
            rcases hv with rfl | rfl | rfl | rfl <;>
            aesop
        · simp [habne, hca.1, hcb.1, hda.1, hdb.1, hdc.1,
            Ne.symm habne, Ne.symm hca.1, Ne.symm hcb.1, Ne.symm hda.1,
            Ne.symm hdb.1, Ne.symm hdc.1]
      exact hindep _ hfour
    have hcN := hN c
    have hu := Finset.card_union_add_card_inter S (N c)
    rw [hcover] at hu
    have huni : (Finset.univ : Finset (Fin 128)).card = 128 := by decide
    have hi : (S ∩ N c).card = 0 := by omega
    exact Finset.disjoint_left.mpr (by
      intro z hz hzc
      have : z ∈ S ∩ N c := Finset.mem_inter.mpr ⟨hz, hzc⟩
      have he : S ∩ N c = ∅ := Finset.card_eq_zero.mp hi
      simpa [he] using this)
  have hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S := by
    intro u hu v huv
    by_contra hv
    have huN : u ∈ N v := (hNmem v u).2 (Or.inr huv.symm)
    exact Finset.disjoint_left.mp (hcS v hv) hu huN
  have hout : ∃ x, x ∉ S := by
    by_contra h
    push_neg at h
    have he : S = Finset.univ := by ext x; simp [h x]
    rw [he] at hcap
    norm_num at hcap
  obtain ⟨z, hz⟩ := hout
  have hreach := hconn a z
  obtain ⟨p⟩ := hreach
  have hwalk : ∀ {u v}, (p : G.Walk u v) → u ∈ S → v ∈ S := by
    intro u v p
    induction p with
    | nil => intro h; exact h
    | cons h p ih => intro hu; exact ih (hclosed _ hu _ h)
  exact hz (hwalk p haS)
