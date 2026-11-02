import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# connected_independence_local_clique_card_bound

Topic: graphs   Node: 31d8363efa04

Provenance: helper lemma. General auxiliary-graph route for directed cycle packing, using Mathlib SimpleGraph.colorable_of_cliqueFree_lt_minDegree; experiment 12548 checks sharp examples.

Let r and s be integers at least three and let d be an integer with 3r+3s<d+10. A connected finite simple graph with independence number at most s, maximum degree at most d, and every edge in an r-vertex clique has at most sd−r+2 vertices.
-/

theorem cicb_dense (s d r n : ℕ) (hs : 3 ≤ s) (hgap : 3 * r + 3 * s < d + 10)
    (hn : s * d + 3 ≤ n + r) (hnd : d + 1 < n) :
    (3 * s - 4) * n / (3 * s - 1) < n - 1 - d := by
  obtain ⟨a, rfl⟩ : ∃ a, s = a + 3 := ⟨s - 3, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 + d := ⟨n - 1 - d, by omega⟩
  have h1 : 3 * (a + 3) - 4 = 3 * a + 5 := by omega
  have h2 : 3 * (a + 3) - 1 = 3 * a + 8 := by omega
  have h3 : e + 1 + d - 1 - d = e := by omega
  rw [h1, h2, h3, Nat.div_lt_iff_lt_mul (by omega)]
  nlinarith

theorem connected_independence_local_clique_card_bound
    (r s d : ℕ) (hr : 3 ≤ r) (hs : 3 ≤ s) (hgap : 3 * r + 3 * s < d + 10)
    (α : Type) [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (hindep : G.IndepSetFree (s + 1))
    (hdeg : ∀ v, G.degree v ≤ d)
    (hclique : ∀ u v, G.Adj u v → ∃ S : Finset α,
      S.card = r ∧ u ∈ S ∧ v ∈ S ∧ G.IsClique (S : Set α)) :
    Fintype.card α ≤ s * d - r + 2 := by
  classical
  letI : Nonempty α := hconn.nonempty
  by_contra hn
  have h3d : 3 * d ≤ s * d := Nat.mul_le_mul_right d hs
  have hn' : s * d + 3 ≤ Fintype.card α + r := by omega
  have hnd : d + 1 < Fintype.card α := by omega
  have hmin : Fintype.card α - 1 - d ≤ Gᶜ.minDegree := by
    apply Gᶜ.le_minDegree_of_forall_le_degree
    intro v
    rw [G.degree_compl]
    have hd := hdeg v
    omega
  have hf : Gᶜ.CliqueFree (s + 1) := by simpa using hindep
  have hdense : (3 * s - 4) * Fintype.card α / (3 * s - 1) < Gᶜ.minDegree :=
    lt_of_lt_of_le (cicb_dense s d r _ hs hgap hn' hnd) hmin
  have hcolor : Gᶜ.Colorable s :=
    SimpleGraph.colorable_of_cliqueFree_lt_minDegree (G := Gᶜ) (r := s) hf hdense
  obtain ⟨col⟩ := hcolor
  let P : Fin s → Finset α := fun i => Finset.univ.filter fun x => col x = i
  have hmem : ∀ i x, x ∈ P i ↔ col x = i := by intro i x; simp [P]
  have hinside : ∀ (i : Fin s) (x : α), x ∈ P i → ∀ y ∈ P i, x ≠ y → G.Adj x y := by
    intro i x hx y hy hxy
    have hxe := (hmem i x).mp hx
    have hye := (hmem i y).mp hy
    by_contra h
    have hcomp : Gᶜ.Adj x y := ⟨hxy, h⟩
    have hncol := col.valid hcomp
    exact hncol (hxe.trans hye.symm)
  have hsum : ∑ i, (P i).card = Fintype.card α := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun x : α => col x) (s := Finset.univ) (t := Finset.univ) (by simp)
    simpa [P] using h.symm
  have hpartcap : ∀ i, (P i).card ≤ d + 1 := by
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
  have hpartsmall : ∀ i, (P i).card ≤ d := by
    intro i
    by_contra h
    have hs' : (P i).card = d + 1 := by have := hpartcap i; omega
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
    rw [hall] at hs'
    simp at hs'
    omega
  have hcross : ∃ x y, G.Adj x y ∧ col x ≠ col y := by
    by_contra h
    push_neg at h
    have hwalk : ∀ {u v}, G.Walk u v → col u = col v := by
      intro u v p
      induction p with
      | nil => rfl
      | cons hab p ih => exact (h _ _ hab).trans ih
    obtain ⟨x⟩ := (inferInstance : Nonempty α)
    have hall : P (col x) = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro v
      obtain ⟨p⟩ := hconn x v
      exact (hmem _ v).mpr (hwalk p).symm
    have := hpartsmall (col x)
    rw [hall, Finset.card_univ] at this
    omega
  obtain ⟨x, y, hxy, hnecol⟩ := hcross
  obtain ⟨Q, hQcard, hxQ, hyQ, hQcl⟩ := hclique x y hxy
  have hQbound : ∀ i u, u ∈ P i → u ∈ Q →
      (P i).card + r ≤ d + 1 + (Q ∩ P i).card := by
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
    have hr' := Finset.card_sdiff_add_card_inter Q (P i)
    have hd := hdeg u
    change ((P i).erase u).card + R.card ≤ G.degree u at hcard
    change R.card + (Q ∩ P i).card = Q.card at hr'
    omega
  have hxi : x ∈ P (col x) := (hmem (col x) x).2 rfl
  have hyj : y ∈ P (col y) := (hmem (col y) y).2 rfl
  have hxbound := hQbound (col x) x hxi hxQ
  have hybound := hQbound (col y) y hyj hyQ
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
  -- the two parts of the cross edge, and at most d in each of the others
  have hrest : ∑ i ∈ (Finset.univ.erase (col x)).erase (col y), (P i).card ≤ (s - 2) * d := by
    have hcardrest : ((Finset.univ.erase (col x)).erase (col y)).card = s - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hnecol.symm, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    calc ∑ i ∈ (Finset.univ.erase (col x)).erase (col y), (P i).card
        ≤ ∑ _i ∈ (Finset.univ.erase (col x)).erase (col y), d :=
          Finset.sum_le_sum fun i _ => hpartsmall i
      _ = (s - 2) * d := by rw [Finset.sum_const, hcardrest, smul_eq_mul]
  have hsplit : ∑ i, (P i).card = (P (col x)).card + ((P (col y)).card +
      ∑ i ∈ (Finset.univ.erase (col x)).erase (col y), (P i).card) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (col x)),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hnecol.symm, Finset.mem_univ _⟩)]
  have hsd : (s - 2) * d + 2 * d = s * d := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  omega
