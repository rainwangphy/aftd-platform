import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberEqZeroOfPackingNumberEqZero
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberEqZeroOfCliqueFree
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_triangle_cover_number_le_two_of_packing_number_le_one

Topic: graphs   Node: 0a9046f62a34

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number

Tuza's conjecture holds for graphs with packing number at most 1: if ν(G) ≤ 1, then τ(G) ≤ 2.
-/

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_card_pair_le {α : Type*} [DecidableEq α] (x y : α) :
    ({x, y} : Finset α).card ≤ 2 := by
  apply (Finset.card_insert_le _ _).trans
  simp

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_card_singleton_le {α : Type*} (x : α) :
    ({x} : Finset α).card ≤ 2 := by
  simp

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_cover_le_of_exists {V : Type*} (G : SimpleGraph V) (F : Finset (Sym2 V))
    (hFedge : ∀ e ∈ F, e ∈ G.edgeSet)
    (hcover : ∀ (t : Finset V), G.IsNClique 3 t → ∃ e ∈ F, ∀ x ∈ e, x ∈ t)
    (hcard : F.card ≤ 2) :
    simple_graph_triangle_cover_number G ≤ 2 := by
  have hmem : F.card ∈ {n | ∃ (F' : Finset (Sym2 V)), (∀ e ∈ F', e ∈ G.edgeSet) ∧
      (∀ (t : Finset V), G.IsNClique 3 t → ∃ e ∈ F', ∀ x ∈ e, x ∈ t) ∧ F'.card = n} :=
    ⟨F, hFedge, hcover, rfl⟩
  have hle : simple_graph_triangle_cover_number G ≤ F.card := Nat.sInf_le hmem
  omega

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_mem_cover_pair_iff {V : Type*} [DecidableEq V] (u1 v1 u2 v2 : V) (t : Finset V) :
    (∃ e ∈ ({s(u1, v1), s(u2, v2)} : Finset (Sym2 V)), ∀ x ∈ e, x ∈ t) ↔
    ((u1 ∈ t ∧ v1 ∈ t) ∨ (u2 ∈ t ∧ v2 ∈ t)) := by
  constructor
  · rintro ⟨e, he, h⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · left
      exact ⟨h u1 (by simp), h v1 (by simp)⟩
    · right
      exact ⟨h u2 (by simp), h v2 (by simp)⟩
  · rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
    · refine ⟨s(u1, v1), by simp, ?_⟩
      intro x hx; rw [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> assumption
    · refine ⟨s(u2, v2), by simp, ?_⟩
      intro x hx; rw [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> assumption

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_mem_cover_singleton_iff {V : Type*} [DecidableEq V] (u v : V) (t : Finset V) :
    (∃ e ∈ ({s(u, v)} : Finset (Sym2 V)), ∀ x ∈ e, x ∈ t) ↔ (u ∈ t ∧ v ∈ t) := by
  constructor
  · rintro ⟨e, he, h⟩
    simp only [Finset.mem_singleton] at he
    subst he
    exact ⟨h u (by simp), h v (by simp)⟩
  · rintro ⟨hu, hv⟩
    refine ⟨s(u, v), by simp, ?_⟩
    intro x hx; rw [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> assumption

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangles_intersect_ge_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h : simple_graph_triangle_packing_number G ≤ 1)
    (t1 t2 : Finset V) (h1 : G.IsNClique 3 t1) (h2 : G.IsNClique 3 t2) :
    2 ≤ (t1 ∩ t2).card := by
  by_contra hlt
  have hlt : (t1 ∩ t2).card ≤ 1 := by omega
  have hne : t1 ≠ t2 := by
    rintro rfl
    have := h1.card_eq
    rw [Finset.inter_self] at hlt
    omega
  set T : Finset (Finset V) := {t1, t2}
  have hTcard : T.card = 2 := Finset.card_pair hne
  have hTclique : ∀ t ∈ T, G.IsNClique 3 t := by
    intro t ht
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> assumption
  have hTpairwise : (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) := by
    intro s hs t ht hst
    simp only [T, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · contradiction
    · exact hlt
    · rw [Finset.inter_comm]
      exact hlt
    · contradiction
  set P : Set ℕ := {n | ∃ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) ∧
    (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n}
  have h2mem : 2 ∈ P := ⟨T, hTclique, hTpairwise, hTcard⟩
  have hbdd : BddAbove P := by
    refine ⟨(Finset.univ : Finset (Finset V)).card, ?_⟩
    rintro n ⟨T', -, -, rfl⟩
    exact Finset.card_le_univ T'
  have hle : 2 ≤ simple_graph_triangle_packing_number G := le_csSup hbdd h2mem
  omega

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangle_inter_three {V : Type*} [DecidableEq V] {a b c : V}
    {t : Finset V} (hcard : 2 ≤ (t ∩ {a, b, c}).card) :
    (a ∈ t ∧ b ∈ t) ∨ (a ∈ t ∧ c ∈ t) ∨ (b ∈ t ∧ c ∈ t) := by
  have hs : (t ∩ {a, b, c}) ⊆ {a, b, c} := Finset.inter_subset_right
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 hcard
  have hua := hs hu
  have hva := hs hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hua hva
  rw [Finset.mem_inter] at hu hv
  rcases hua with rfl | rfl | rfl <;> rcases hva with rfl | rfl | rfl
  · contradiction
  · left; exact ⟨hu.1, hv.1⟩
  · right; left; exact ⟨hu.1, hv.1⟩
  · left; exact ⟨hv.1, hu.1⟩
  · contradiction
  · right; right; exact ⟨hu.1, hv.1⟩
  · right; left; exact ⟨hv.1, hu.1⟩
  · right; right; exact ⟨hv.1, hu.1⟩
  · contradiction

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_eq_of_card_three_of_mem_three {V : Type*} [DecidableEq V] {x y z : V}
    {t : Finset V} (ht : t.card = 3) (hx : x ∈ t) (hy : y ∈ t) (hz : z ∈ t)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    t = {x, y, z} := by
  have hsub : ({x, y, z} : Finset V) ⊆ t := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl <;> assumption
  have hcard : ({x, y, z} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hyz]
    simp [hxy, hxz]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [ht, hcard])).symm

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_eq_three_of_mem_mem_not_mem {V : Type*} [DecidableEq V] {a b c : V}
    {t : Finset V} (ht : t.card = 3) (hb : b ∈ t) (hc : c ∈ t) (hbc : b ≠ c)
    (ha : a ∉ t) :
    ∃ d, d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ t = {b, c, d} := by
  have h2 : ({b, c} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hdiff : (t \ {b, c}).card = 1 := by
    rw [Finset.card_sdiff_of_subset h2, Finset.card_pair hbc, ht]
  obtain ⟨d, hd⟩ := Finset.card_eq_one.1 hdiff
  have hdt : d ∈ t := (Finset.mem_sdiff.1 (hd.symm ▸ Finset.mem_singleton_self d)).1
  have hdnot : d ∉ ({b, c} : Finset V) := (Finset.mem_sdiff.1 (hd.symm ▸ Finset.mem_singleton_self d)).2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hdnot
  refine ⟨d, ?_, hdnot.1, hdnot.2, ?_⟩
  · rintro rfl; exact ha hdt
  · ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases hxbc : x ∈ ({b, c} : Finset V)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hxbc
        rcases hxbc with rfl | rfl
        · left; rfl
        · right; left; rfl
      · right; right
        have : x ∈ t \ {b, c} := Finset.mem_sdiff.2 ⟨hx, hxbc⟩
        rw [hd] at this
        exact Finset.mem_singleton.1 this
    · rintro (rfl | rfl | rfl) <;> assumption

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_t3_cases {V : Type*} [DecidableEq V] {a b c d : V}
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (_hbc : b ≠ c)
    {t3 : Finset V} (ht3 : t3.card = 3)
    (h1 : 2 ≤ (t3 ∩ {a, b, c}).card)
    (h2 : 2 ≤ (t3 ∩ {b, c, d}).card)
    (hnot : ¬ (b ∈ t3 ∧ c ∈ t3)) :
    t3 = {a, b, d} ∨ t3 = {a, c, d} := by
  have hi1 := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangle_inter_three h1
  have hi2 := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangle_inter_three h2
  rcases hi1 with ⟨ha, hb⟩ | ⟨ha, hc⟩ | hbc'
  · have hc : c ∉ t3 := fun hc => hnot ⟨hb, hc⟩
    rcases hi2 with ⟨-, hc'⟩ | ⟨-, hd⟩ | ⟨hc', -⟩
    · exact absurd hc' hc
    · left
      exact simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_eq_of_card_three_of_mem_three ht3 ha hb hd hab hda.symm hdb.symm
    · exact absurd hc' hc
  · have hb : b ∉ t3 := fun hb => hnot ⟨hb, hc⟩
    rcases hi2 with ⟨hb', -⟩ | ⟨hb', -⟩ | ⟨-, hd⟩
    · exact absurd hb' hb
    · exact absurd hb' hb
    · right
      exact simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_eq_of_card_three_of_mem_three ht3 ha hc hd hac hda.symm hdc.symm
  · exact absurd hbc' hnot

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_cover_k4_case_1 {V : Type*} [DecidableEq V] {a b c d : V}
    {t : Finset V}
    (h1 : 2 ≤ (t ∩ {a, b, c}).card)
    (h2 : 2 ≤ (t ∩ {b, c, d}).card)
    (h3 : 2 ≤ (t ∩ {a, b, d}).card) :
    (a ∈ t ∧ b ∈ t) ∨ (c ∈ t ∧ d ∈ t) := by
  by_contra h
  have hab : ¬ (a ∈ t ∧ b ∈ t) := fun h' => h (Or.inl h')
  have hcd : ¬ (c ∈ t ∧ d ∈ t) := fun h' => h (Or.inr h')
  have hi1 : c ∈ t := by
    rcases simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangle_inter_three h1 with ⟨ha, hb⟩ | ⟨-, hc⟩ | ⟨-, hc⟩
    · exact absurd ⟨ha, hb⟩ hab
    · exact hc
    · exact hc
  have hd : d ∉ t := fun hd => hcd ⟨hi1, hd⟩
  have hi2 : b ∈ t := by
    rcases simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangle_inter_three h2 with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨-, hd'⟩
    · exact hb
    · exact hb
    · exact absurd hd' hd
  have ha : a ∉ t := fun ha => hab ⟨ha, hi2⟩
  have hsub : (t ∩ {a, b, d}) ⊆ {b} := by
    intro x hx
    rw [Finset.mem_inter] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 ha
    · simp
    · exact absurd hx.1 hd
  have hcard : (t ∩ {a, b, d}).card ≤ 1 := by
    calc (t ∩ {a, b, d}).card ≤ ({b} : Finset V).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton b
  omega

lemma simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_cover_k4_case_2 {V : Type*} [DecidableEq V] {a b c d : V}
    {t : Finset V}
    (h1 : 2 ≤ (t ∩ {a, b, c}).card)
    (h2 : 2 ≤ (t ∩ {b, c, d}).card)
    (h3 : 2 ≤ (t ∩ {a, c, d}).card) :
    (a ∈ t ∧ c ∈ t) ∨ (b ∈ t ∧ d ∈ t) := by
  by_contra h
  have hac : ¬ (a ∈ t ∧ c ∈ t) := fun h' => h (Or.inl h')
  have hbd : ¬ (b ∈ t ∧ d ∈ t) := fun h' => h (Or.inr h')
  have hi1 : b ∈ t := by
    rcases simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangle_inter_three h1 with ⟨-, hb⟩ | ⟨ha, hc⟩ | ⟨hb, -⟩
    · exact hb
    · exact absurd ⟨ha, hc⟩ hac
    · exact hb
  have hd : d ∉ t := fun hd => hbd ⟨hi1, hd⟩
  have hi2 : c ∈ t := by
    rcases simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangle_inter_three h2 with ⟨-, hc⟩ | ⟨-, hd'⟩ | ⟨hc, -⟩
    · exact hc
    · exact absurd hd' hd
    · exact hc
  have ha : a ∉ t := fun ha => hac ⟨ha, hi2⟩
  have hsub : (t ∩ {a, c, d}) ⊆ {c} := by
    intro x hx
    rw [Finset.mem_inter] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx.2 with rfl | rfl | rfl
    · exact absurd hx.1 ha
    · simp
    · exact absurd hx.1 hd
  have hcard : (t ∩ {a, c, d}).card ≤ 1 := by
    calc (t ∩ {a, c, d}).card ≤ ({c} : Finset V).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton c
  omega

/-- Tuza's conjecture holds for graphs with packing number at most 1: if ν(G) ≤ 1, then τ(G) ≤ 2. -/
theorem simple_graph_triangle_cover_number_le_two_of_packing_number_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h : simple_graph_triangle_packing_number G ≤ 1) :
    simple_graph_triangle_cover_number G ≤ 2 := by
  classical
  by_cases hcf : G.CliqueFree 3
  · rw [simple_graph_triangle_cover_number_eq_zero_of_clique_free G hcf]
    exact Nat.zero_le 2
  · obtain ⟨t1, ht1⟩ : ∃ t, G.IsNClique 3 t := by
      by_contra hno
      apply hcf
      intro t ht
      exact hno ⟨t, ht⟩
    obtain ⟨a, b, c, hab, hac, hbc, ht1eq⟩ := Finset.card_eq_three.1 ht1.card_eq
    have hcl1 := ht1.isClique
    rw [ht1eq] at hcl1
    have ha_t1 : a ∈ ({a, b, c} : Finset V) := by simp
    have hb_t1 : b ∈ ({a, b, c} : Finset V) := by simp
    have hc_t1 : c ∈ ({a, b, c} : Finset V) := by simp
    have hG_ab : s(a, b) ∈ G.edgeSet := hcl1 ha_t1 hb_t1 hab
    have hG_ac : s(a, c) ∈ G.edgeSet := hcl1 ha_t1 hc_t1 hac
    have hG_bc : s(b, c) ∈ G.edgeSet := hcl1 hb_t1 hc_t1 hbc
    by_cases hcov1 : ∀ t, G.IsNClique 3 t → ∃ e ∈ ({s(a, b), s(a, c)} : Finset (Sym2 V)), ∀ x ∈ e, x ∈ t
    · refine simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_cover_le_of_exists G {s(a, b), s(a, c)} ?_ hcov1 (simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_card_pair_le _ _)
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    · obtain ⟨t2, ht2, hnot1⟩ : ∃ t, G.IsNClique 3 t ∧ ¬ ∃ e ∈ ({s(a, b), s(a, c)} : Finset (Sym2 V)), ∀ x ∈ e, x ∈ t := by
        by_contra hno
        apply hcov1
        intro t ht
        by_contra hno'
        exact hno ⟨t, ht, hno'⟩
      rw [simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_mem_cover_pair_iff] at hnot1
      have hinter12 : 2 ≤ (t2 ∩ {a, b, c}).card := by
        have := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangles_intersect_ge_two G h t1 t2 ht1 ht2
        rwa [ht1eq, Finset.inter_comm] at this
      have hnotab : ¬ (a ∈ t2 ∧ b ∈ t2) := fun h => hnot1 (Or.inl h)
      have hnotac : ¬ (a ∈ t2 ∧ c ∈ t2) := fun h => hnot1 (Or.inr h)
      have hbc2 : b ∈ t2 ∧ c ∈ t2 := by
        rcases simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangle_inter_three hinter12 with ⟨ha, hb⟩ | ⟨ha, hc⟩ | hbc'
        · exact absurd ⟨ha, hb⟩ hnotab
        · exact absurd ⟨ha, hc⟩ hnotac
        · exact hbc'
      have ha2 : a ∉ t2 := fun ha => hnotab ⟨ha, hbc2.1⟩
      obtain ⟨d, hda, hdb, hdc, ht2eq⟩ := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_eq_three_of_mem_mem_not_mem ht2.card_eq hbc2.1 hbc2.2 hbc ha2
      have hcl2 := ht2.isClique
      rw [ht2eq] at hcl2
      have hb_t2 : b ∈ ({b, c, d} : Finset V) := by simp
      have hc_t2 : c ∈ ({b, c, d} : Finset V) := by simp
      have hd_t2 : d ∈ ({b, c, d} : Finset V) := by simp
      have hG_cd : s(c, d) ∈ G.edgeSet := hcl2 hc_t2 hd_t2 hdc.symm
      have hG_bd : s(b, d) ∈ G.edgeSet := hcl2 hb_t2 hd_t2 hdb.symm
      by_cases hcov2 : ∀ t, G.IsNClique 3 t → ∃ e ∈ ({s(b, c)} : Finset (Sym2 V)), ∀ x ∈ e, x ∈ t
      · refine simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_cover_le_of_exists G {s(b, c)} ?_ hcov2 (simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_card_singleton_le _)
        intro e he
        simp only [Finset.mem_singleton] at he
        subst he
        exact hG_bc
      · obtain ⟨t3, ht3, hnot2⟩ : ∃ t, G.IsNClique 3 t ∧ ¬ ∃ e ∈ ({s(b, c)} : Finset (Sym2 V)), ∀ x ∈ e, x ∈ t := by
          by_contra hno
          apply hcov2
          intro t ht
          by_contra hno'
          exact hno ⟨t, ht, hno'⟩
        rw [simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_mem_cover_singleton_iff] at hnot2
        have hinter13 : 2 ≤ (t3 ∩ {a, b, c}).card := by
          have := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangles_intersect_ge_two G h t1 t3 ht1 ht3
          rwa [ht1eq, Finset.inter_comm] at this
        have hinter23 : 2 ≤ (t3 ∩ {b, c, d}).card := by
          have := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangles_intersect_ge_two G h t2 t3 ht2 ht3
          rwa [ht2eq, Finset.inter_comm] at this
        have ht3cases := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_t3_cases hda hdb hdc hab hac hbc ht3.card_eq hinter13 hinter23 hnot2
        rcases ht3cases with ht3_1 | ht3_2
        · -- Case 1: t3 = {a, b, d}
          have hcov : ∀ t, G.IsNClique 3 t → ∃ e ∈ ({s(a, b), s(c, d)} : Finset (Sym2 V)), ∀ x ∈ e, x ∈ t := by
            intro t ht
            rw [simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_mem_cover_pair_iff]
            have h1t : 2 ≤ (t ∩ {a, b, c}).card := by
              have := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangles_intersect_ge_two G h t1 t ht1 ht
              rwa [ht1eq, Finset.inter_comm] at this
            have h2t : 2 ≤ (t ∩ {b, c, d}).card := by
              have := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangles_intersect_ge_two G h t2 t ht2 ht
              rwa [ht2eq, Finset.inter_comm] at this
            have h3t : 2 ≤ (t ∩ {a, b, d}).card := by
              have := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangles_intersect_ge_two G h t3 t ht3 ht
              rwa [ht3_1, Finset.inter_comm] at this
            exact simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_cover_k4_case_1 h1t h2t h3t
          refine simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_cover_le_of_exists G {s(a, b), s(c, d)} ?_ hcov (simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_card_pair_le _ _)
          intro e he
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl <;> assumption
        · -- Case 2: t3 = {a, c, d}
          have hcov : ∀ t, G.IsNClique 3 t → ∃ e ∈ ({s(a, c), s(b, d)} : Finset (Sym2 V)), ∀ x ∈ e, x ∈ t := by
            intro t ht
            rw [simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_mem_cover_pair_iff]
            have h1t : 2 ≤ (t ∩ {a, b, c}).card := by
              have := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangles_intersect_ge_two G h t1 t ht1 ht
              rwa [ht1eq, Finset.inter_comm] at this
            have h2t : 2 ≤ (t ∩ {b, c, d}).card := by
              have := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangles_intersect_ge_two G h t2 t ht2 ht
              rwa [ht2eq, Finset.inter_comm] at this
            have h3t : 2 ≤ (t ∩ {a, c, d}).card := by
              have := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_triangles_intersect_ge_two G h t3 t ht3 ht
              rwa [ht3_2, Finset.inter_comm] at this
            exact simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_cover_k4_case_2 h1t h2t h3t
          refine simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_cover_le_of_exists G {s(a, c), s(b, d)} ?_ hcov (simple_graph_triangle_cover_number_le_two_of_packing_number_le_one_card_pair_le _ _)
          intro e he
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl <;> assumption
