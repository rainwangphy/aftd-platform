import AFTD.Prelude

/-!
# connected_graph_indep_three_degree_42_seven_cliques_card_le_121

Topic: graphs   Node: d3d7baffe56c

Provenance: helper lemma. Auxiliary-graph refinement for OP-110 using Mathlib SimpleGraph.colorable_of_cliqueFree_lt_minDegree and the seven-vertex out-neighborhood cliques. Experiment 12531 shows the abstract bound is sharp.

A connected finite simple graph with independence number at most three, maximum degree at most 42, and every edge in a seven-vertex clique has at most 121 vertices.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem connected_graph_indep_three_degree_42_seven_cliques_card_le_121
    (α : Type) [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (hindep : G.IndepSetFree 4)
    (hdeg : ∀ v, G.degree v ≤ 42)
    (hclique : ∀ u v, G.Adj u v → ∃ S : Finset α,
      S.card = 7 ∧ u ∈ S ∧ v ∈ S ∧ G.IsClique (S : Set α)) :
    Fintype.card α ≤ 121 := by
  classical
  letI : Nonempty α := hconn.nonempty
  by_contra hn
  have hn' : 122 ≤ Fintype.card α := by omega
  have hmin : Fintype.card α - 43 ≤ Gᶜ.minDegree := by
    apply Gᶜ.le_minDegree_of_forall_le_degree
    intro v
    rw [G.degree_compl]
    have hd := hdeg v
    omega
  have hf : Gᶜ.CliqueFree 4 := by simpa using hindep
  have hdense : (3 * 3 - 4) * Fintype.card α / (3 * 3 - 1) < Gᶜ.minDegree := by
    omega
  have hcolor : Gᶜ.Colorable 3 :=
    SimpleGraph.colorable_of_cliqueFree_lt_minDegree (G := Gᶜ) (r := 3) hf hdense
  obtain ⟨col⟩ := hcolor
  let P : Fin 3 → Finset α := fun i => Finset.univ.filter fun x => col x = i
  have hmem : ∀ i x, x ∈ P i ↔ col x = i := by intro i x; simp [P]
  have hinside : ∀ (i : Fin 3) (x : α), x ∈ P i → ∀ y ∈ P i, x ≠ y → G.Adj x y := by
    intro i x hx y hy hxy
    have hxe := (hmem i x).mp hx
    have hye := (hmem i y).mp hy
    by_contra h
    have hcomp : Gᶜ.Adj x y := ⟨hxy, h⟩
    have hncol := col.valid hcomp
    exact hncol (hxe.trans hye.symm)
  have hsum : (P 0).card + (P 1).card + (P 2).card = Fintype.card α := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun x : α => col x) (s := Finset.univ) (t := Finset.univ) (by simp)
    simpa [P, Fin.sum_univ_three] using h.symm
  have hpartcap : ∀ i, (P i).card ≤ 43 := by
    intro i
    by_cases hne : (P i).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hsub : (P i).erase x ⊆ G.neighborFinset x := by
        intro y hy
        have hy' := Finset.mem_erase.mp hy
        exact (SimpleGraph.mem_neighborFinset G x y).mpr
          (hinside i x hx y hy'.2 hy'.1.symm)
      have hc := Finset.card_le_card hsub
      have he := Finset.card_erase_add_one hx
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
      have hd := hdeg x
      omega
    · have he : P i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [he]
  have hpartsmall : ∀ i, (P i).card ≤ 42 := by
    intro i
    by_contra h
    have hs : (P i).card = 43 := by have := hpartcap i; omega
    have hne : (P i).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hne
    have hclosed : ∀ u ∈ P i, ∀ v, G.Adj u v → v ∈ P i := by
      intro u hu v huv
      have hsub : (P i).erase u ⊆ G.neighborFinset u := by
        intro z hz
        have hz' := Finset.mem_erase.mp hz
        exact (SimpleGraph.mem_neighborFinset G u z).mpr
          (hinside i u hu z hz'.2 hz'.1.symm)
      have he := Finset.card_erase_add_one hu
      have hcard : (G.neighborFinset u).card ≤ ((P i).erase u).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        have hd := hdeg u
        omega
      have heq := Finset.eq_of_subset_of_card_le hsub hcard
      have hv : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset G u v).mpr huv
      rw [← heq] at hv
      exact (Finset.mem_erase.mp hv).2
    have hwalk : ∀ {u v}, G.Walk u v → u ∈ P i → v ∈ P i := by
      intro u v p
      induction p with
      | nil => intro hu; exact hu
      | cons h p ih => intro hu; exact ih (hclosed _ hu _ h)
    have hall : P i = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro v
      obtain ⟨p⟩ := hconn x v
      exact hwalk p hx
    rw [hall] at hs
    simp at hs
    omega
  have hpartlower : ∀ i, 38 ≤ (P i).card := by
    intro i
    have h0 := hpartsmall 0
    have h1 := hpartsmall 1
    have h2 := hpartsmall 2
    fin_cases i
    · change 38 ≤ (P 0).card; omega
    · change 38 ≤ (P 1).card; omega
    · change 38 ≤ (P 2).card; omega
  have hpair : ∀ i j : Fin 3, i ≠ j → 80 ≤ (P i).card + (P j).card := by
    intro i j hij
    have h0 := hpartsmall 0
    have h1 := hpartsmall 1
    have h2 := hpartsmall 2
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change 80 ≤ (P 0).card + (P 1).card; omega
    · change 80 ≤ (P 0).card + (P 2).card; omega
    · change 80 ≤ (P 1).card + (P 0).card; omega
    · exact (hij rfl).elim
    · change 80 ≤ (P 1).card + (P 2).card; omega
    · change 80 ≤ (P 2).card + (P 0).card; omega
    · change 80 ≤ (P 2).card + (P 1).card; omega
    · exact (hij rfl).elim
  have hcross : ∃ x y, G.Adj x y ∧ col x ≠ col y := by
    by_contra h
    push_neg at h
    have hwalk : ∀ {u v}, G.Walk u v → col u = col v := by
      intro u v p
      induction p with
      | nil => rfl
      | cons hab p ih => exact (h _ _ hab).trans ih
    have h0 : (P 0).Nonempty := Finset.card_pos.mp (by have := hpartlower 0; omega)
    have h1 : (P 1).Nonempty := Finset.card_pos.mp (by have := hpartlower 1; omega)
    obtain ⟨x, hx⟩ := h0
    obtain ⟨y, hy⟩ := h1
    obtain ⟨p⟩ := hconn x y
    have hh := hwalk p
    have hx' := (hmem 0 x).mp hx
    have hy' := (hmem 1 y).mp hy
    rw [hx', hy'] at hh
    exact (by decide : (0 : Fin 3) ≠ 1) hh
  obtain ⟨x, y, hxy, hnecol⟩ := hcross
  obtain ⟨Q, hQcard, hxQ, hyQ, hQcl⟩ := hclique x y hxy
  have hQbound : ∀ i u, u ∈ P i → u ∈ Q →
      (P i).card + 7 ≤ 43 + (Q ∩ P i).card := by
    intro i u huP huQ
    let E := (P i).erase u
    let R := Q \ P i
    have hdis : Disjoint E R := by
      apply Finset.disjoint_left.mpr
      intro z hzE hzR
      have hzP := (Finset.mem_erase.mp hzE).2
      have hznot := (Finset.mem_sdiff.mp hzR).2
      exact hznot hzP
    have hsub : E ∪ R ⊆ G.neighborFinset u := by
      intro z hz
      rcases Finset.mem_union.mp hz with hzE | hzR
      · have hz' := Finset.mem_erase.mp hzE
        exact (SimpleGraph.mem_neighborFinset G u z).mpr
          (hinside i u huP z hz'.2 hz'.1.symm)
      · have hz' := Finset.mem_sdiff.mp hzR
        have hne : u ≠ z := by intro he; subst z; exact hz'.2 huP
        exact (SimpleGraph.mem_neighborFinset G u z).mpr (hQcl huQ hz'.1 hne)
    have hcard := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_union_of_disjoint hdis] at hcard
    have he := Finset.card_erase_add_one huP
    have hr := Finset.card_sdiff_add_card_inter Q (P i)
    have hd := hdeg u
    change ((P i).erase u).card + R.card ≤ G.degree u at hcard
    change R.card + (Q ∩ P i).card = Q.card at hr
    omega
  have hxi : x ∈ P (col x) := (hmem (col x) x).2 rfl
  have hyj : y ∈ P (col y) := (hmem (col y) y).2 rfl
  have hxbound := hQbound (col x) x hxi hxQ
  have hybound := hQbound (col y) y hyj hyQ
  have hpairs := hpair (col x) (col y) hnecol
  have hdis : Disjoint (Q ∩ P (col x)) (Q ∩ P (col y)) := by
    apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    have h1 := (hmem (col x) z).mp (Finset.mem_inter.mp hz1).2
    have h2 := (hmem (col y) z).mp (Finset.mem_inter.mp hz2).2
    exact hnecol (h1.symm.trans h2)
  have hsub : (Q ∩ P (col x)) ∪ (Q ∩ P (col y)) ⊆ Q := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h <;> exact (Finset.mem_inter.mp h).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, hQcard] at hc
  omega
