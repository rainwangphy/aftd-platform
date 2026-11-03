import AFTD.Prelude

/-!
# simple_graph_three_edge_intersecting_triangles_complete_four_clique

Topic: graphs   Node: b0b3fac1422c

Provenance: helper lemma. A graph-specific closure property used in the triangle packing-cover campaign; related work: arXiv:2610.15269, Lemma 3.2. Experiments 13111 and 13112 show that a linear triple system can fail this closure even after small intersecting obstructions are excluded.

If three triangles in a simple graph share an edge pairwise, and the two shared edges of the first triangle are distinct, then their union is a four-vertex clique and the graph contains the distinct fourth triangle, which shares an edge with each of the original three.
-/

open Finset

lemma simple_graph_three_edge_intersecting_triangles_complete_four_clique_card_inter_of_subsets_card_two
    {V : Type*} [DecidableEq V] {s A B : Finset V}
    (hs : s.card = 3) (hA : A ⊆ s) (hB : B ⊆ s)
    (hAc : A.card = 2) (hBc : B.card = 2) (hne : A ≠ B) :
    (A ∩ B).card = 1 := by
  have hunion_sub : A ∪ B ⊆ s := union_subset hA hB
  have hunion_card_le : (A ∪ B).card ≤ 3 := by
    rw [← hs]
    exact card_le_card hunion_sub
  have hne_card : (A ∩ B).card < 2 := by
    by_contra! hle
    have : (A ∩ B).card = 2 := by
      have : A ∩ B ⊆ A := inter_subset_left
      exact le_antisymm (hAc ▸ card_le_card this) hle
    have hAB : A ∩ B = A := eq_of_subset_of_card_le inter_subset_left (by rw [this, hAc])
    have hBA : A ∩ B = B := eq_of_subset_of_card_le inter_subset_right (by rw [this, hBc])
    exact hne (hAB.symm.trans hBA)
  have h_inc_exc : (A ∪ B).card + (A ∩ B).card = A.card + B.card := card_union_add_card_inter A B
  omega

lemma simple_graph_three_edge_intersecting_triangles_complete_four_clique_card_two_eq
    {V : Type*} [DecidableEq V] {s : Finset V} (hs : s.card = 2) {a : V} (ha : a ∈ s) :
    ∃ b : V, b ≠ a ∧ s = {a, b} := by
  have hcard : (s.erase a).card = 1 := by
    rw [card_erase_of_mem ha, hs]
  obtain ⟨b, hb⟩ := card_eq_one.mp hcard
  have hba : b ≠ a := by
    have : b ∈ s.erase a := by rw [hb]; exact mem_singleton_self b
    exact (mem_erase.mp this).1
  have hs_eq : s = {a, b} := by
    rw [← insert_erase ha, hb]
  exact ⟨b, hba, hs_eq⟩

lemma simple_graph_three_edge_intersecting_triangles_complete_four_clique_card_three_eq
    {V : Type*} [DecidableEq V] {s : Finset V} (hs : s.card = 3) {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ∃ c : V, c ≠ a ∧ c ≠ b ∧ s = {a, b, c} := by
  have ha_card : (s.erase a).card = 2 := by
    rw [card_erase_of_mem ha, hs]
  have hb_mem : b ∈ s.erase a := mem_erase.mpr ⟨hab.symm, hb⟩
  have hb_card : ((s.erase a).erase b).card = 1 := by
    rw [card_erase_of_mem hb_mem, ha_card]
  obtain ⟨c, hc⟩ := card_eq_one.mp hb_card
  have hca : c ≠ a := by
    have : c ∈ (s.erase a).erase b := by rw [hc]; exact mem_singleton_self c
    have : c ∈ s.erase a := mem_of_mem_erase this
    exact (mem_erase.mp this).1
  have hcb : c ≠ b := by
    have : c ∈ (s.erase a).erase b := by rw [hc]; exact mem_singleton_self c
    exact (mem_erase.mp this).1
  have hs_eq : s = {a, b, c} := by
    conv_lhs => rw [← insert_erase ha]
    conv_lhs => enter [2]; rw [← insert_erase hb_mem]
    rw [hc]
  exact ⟨c, hca, hcb, hs_eq⟩

lemma simple_graph_three_edge_intersecting_triangles_complete_four_clique_deduce_form
    {V : Type*} [DecidableEq V] (s t u : Finset V)
    (hs : s.card = 3) (ht : t.card = 3) (hu : u.card = 3)
    (hst : (s ∩ t).card = 2) (hsu : (s ∩ u).card = 2) (htu : (t ∩ u).card = 2)
    (hdistinct : s ∩ t ≠ s ∩ u) :
    ∃ a b c d : V,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      s = {a, b, c} ∧ t = {a, b, d} ∧ u = {a, c, d} := by
  have h_inter_eq : (s ∩ t) ∩ (s ∩ u) = s ∩ t ∩ u := by
    ext x; simp only [mem_inter]; tauto
  have h_inter_card : ((s ∩ t) ∩ (s ∩ u)).card = 1 :=
    simple_graph_three_edge_intersecting_triangles_complete_four_clique_card_inter_of_subsets_card_two
      hs inter_subset_left inter_subset_left hst hsu hdistinct
  rw [h_inter_eq] at h_inter_card
  obtain ⟨a, ha_eq⟩ := card_eq_one.mp h_inter_card
  have ha_inter : a ∈ s ∩ t ∩ u := ha_eq ▸ mem_singleton_self a
  have ha_st : a ∈ s ∩ t := (mem_inter.mp ha_inter).1
  have ha_su : a ∈ s ∩ u := by
    have : a ∈ (s ∩ t) ∩ (s ∩ u) := by rw [h_inter_eq]; exact ha_inter
    exact (mem_inter.mp this).2
  obtain ⟨b, hba, hst_eq⟩ :=
    simple_graph_three_edge_intersecting_triangles_complete_four_clique_card_two_eq hst ha_st
  obtain ⟨c, hca, hsu_eq⟩ :=
    simple_graph_three_edge_intersecting_triangles_complete_four_clique_card_two_eq hsu ha_su
  have hab : a ≠ b := hba.symm
  have hac : a ≠ c := hca.symm
  have hbc : b ≠ c := by
    rintro rfl
    exact hdistinct (hst_eq.trans hsu_eq.symm)
  have ha_s : a ∈ s := (mem_inter.mp ha_st).1
  have hb_s : b ∈ s := by
    have : b ∈ s ∩ t := by rw [hst_eq]; simp
    exact (mem_inter.mp this).1
  have hc_s : c ∈ s := by
    have : c ∈ s ∩ u := by rw [hsu_eq]; simp
    exact (mem_inter.mp this).1
  have hs_eq : s = {a, b, c} := by
    have hsub : ({a, b, c} : Finset V) ⊆ s := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hcard : ({a, b, c} : Finset V).card = 3 := by
      simp [hab, hac, hbc]
    exact (eq_of_subset_of_card_le hsub (by rw [hs, hcard])).symm
  have ha_t : a ∈ t := (mem_inter.mp ha_st).2
  have hb_t : b ∈ t := by
    have : b ∈ s ∩ t := by rw [hst_eq]; simp
    exact (mem_inter.mp this).2
  obtain ⟨d, hda, hdb, ht_eq⟩ :=
    simple_graph_three_edge_intersecting_triangles_complete_four_clique_card_three_eq ht ha_t hb_t hab
  have had : a ≠ d := hda.symm
  have hbd : b ≠ d := hdb.symm
  have hcd : c ≠ d := by
    intro hcd_eq
    have hd_in_s : d ∈ s := by rw [hs_eq, ← hcd_eq]; simp
    have hd_in_inter : d ∈ s ∩ t := mem_inter.mpr ⟨hd_in_s, by rw [ht_eq]; simp⟩
    rw [hst_eq] at hd_in_inter
    have hd_cases : d = a ∨ d = b := by simpa using hd_in_inter
    rcases hd_cases with rfl | rfl
    · exact had.symm rfl
    · exact hbd.symm rfl
  have ha_u : a ∈ u := (mem_inter.mp ha_su).2
  have hc_u : c ∈ u := by
    have : c ∈ s ∩ u := by rw [hsu_eq]; simp
    exact (mem_inter.mp this).2
  obtain ⟨e, hea, hec, hu_eq⟩ :=
    simple_graph_three_edge_intersecting_triangles_complete_four_clique_card_three_eq hu ha_u hc_u hac
  have hae : a ≠ e := hea.symm
  have hce : c ≠ e := hec.symm
  have hbe : b ≠ e := by
    intro hbe_eq
    have he_in_s : e ∈ s := by rw [hs_eq, ← hbe_eq]; simp
    have he_in_inter : e ∈ s ∩ u := mem_inter.mpr ⟨he_in_s, by rw [hu_eq]; simp⟩
    rw [hsu_eq] at he_in_inter
    have he_cases : e = a ∨ e = c := by simpa using he_in_inter
    rcases he_cases with rfl | rfl
    · exact hab.symm hbe_eq
    · exact hbc (hbe_eq.trans rfl)
  have hde : d = e := by
    have hsub : ({a, b, d} : Finset V) ∩ ({a, c, e} : Finset V) ⊆ {a, d} := by
      intro x hx
      simp only [mem_inter, mem_insert, mem_singleton] at hx
      rcases hx.1 with rfl | rfl | rfl
      · simp
      · exfalso
        rcases hx.2 with rfl | rfl | rfl
        · exact hab.symm rfl
        · exact hbc rfl
        · exact hbe rfl
      · simp
    have hcard_ad : ({a, d} : Finset V).card ≤ 2 := card_insert_le a {d}
    have heq : ({a, b, d} : Finset V) ∩ ({a, c, e} : Finset V) = {a, d} := by
      apply eq_of_subset_of_card_le hsub
      rw [← ht_eq, ← hu_eq, htu]
      exact hcard_ad
    have hd_in_u : d ∈ ({a, c, e} : Finset V) := by
      have : d ∈ ({a, b, d} : Finset V) ∩ ({a, c, e} : Finset V) := by
        rw [heq]
        exact mem_insert_of_mem (mem_singleton_self d)
      exact (mem_inter.mp this).2
    simp only [mem_insert, mem_singleton] at hd_in_u
    rcases hd_in_u with rfl | rfl | rfl
    · exact False.elim (had.symm rfl)
    · exact False.elim (hcd rfl)
    · rfl
  subst hde
  exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs_eq, ht_eq, hu_eq⟩

theorem simple_graph_three_edge_intersecting_triangles_complete_four_clique {V : Type*} [DecidableEq V] (G : SimpleGraph V) (s t u : Finset V) (hs : G.IsNClique 3 s) (ht : G.IsNClique 3 t) (hu : G.IsNClique 3 u) (hst : (s ∩ t).card = 2) (hsu : (s ∩ u).card = 2) (htu : (t ∩ u).card = 2) (hdistinct : s ∩ t ≠ s ∩ u) : ∃ r : Finset V, G.IsNClique 3 r ∧ r ≠ s ∧ r ≠ t ∧ r ≠ u ∧ (r ∩ s).card = 2 ∧ (r ∩ t).card = 2 ∧ (r ∩ u).card = 2 ∧ (s ∪ t ∪ u).card = 4 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs_eq, ht_eq, hu_eq⟩ :=
    simple_graph_three_edge_intersecting_triangles_complete_four_clique_deduce_form
      s t u hs.card_eq ht.card_eq hu.card_eq hst hsu htu hdistinct
  have hbc_adj : G.Adj b c := by
    have hb : b ∈ (s : Set V) := by rw [hs_eq]; simp
    have hc : c ∈ (s : Set V) := by rw [hs_eq]; simp
    exact hs.isClique hb hc hbc
  have hbd_adj : G.Adj b d := by
    have hb : b ∈ (t : Set V) := by rw [ht_eq]; simp
    have hd : d ∈ (t : Set V) := by rw [ht_eq]; simp
    exact ht.isClique hb hd hbd
  have hcd_adj : G.Adj c d := by
    have hc : c ∈ (u : Set V) := by rw [hu_eq]; simp
    have hd : d ∈ (u : Set V) := by rw [hu_eq]; simp
    exact hu.isClique hc hd hcd
  have hr_clique : G.IsClique (({b, c, d} : Finset V) : Set V) := by
    intro x hx y hy hne
    simp only [Finset.mem_coe, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> try contradiction
    · exact hbc_adj
    · exact hbd_adj
    · exact hbc_adj.symm
    · exact hcd_adj
    · exact hbd_adj.symm
    · exact hcd_adj.symm
  have hr_card : ({b, c, d} : Finset V).card = 3 := by
    simp [hbc, hbd, hcd]
  have hr_nclique : G.IsNClique 3 {b, c, d} := ⟨hr_clique, hr_card⟩
  have hr_ne_s : ({b, c, d} : Finset V) ≠ s := by
    intro h
    have hd : d ∈ s := by rw [← h]; simp
    rw [hs_eq] at hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact had.symm rfl
    · exact hbd.symm rfl
    · exact hcd.symm rfl
  have hr_ne_t : ({b, c, d} : Finset V) ≠ t := by
    intro h
    have hc : c ∈ t := by rw [← h]; simp
    rw [ht_eq] at hc
    simp only [mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact hac.symm rfl
    · exact hbc.symm rfl
    · exact hcd rfl
  have hr_ne_u : ({b, c, d} : Finset V) ≠ u := by
    intro h
    have hb : b ∈ u := by rw [← h]; simp
    rw [hu_eq] at hb
    simp only [mem_insert, mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · exact hab.symm rfl
    · exact hbc rfl
    · exact hbd rfl
  have hr_inter_s : (({b, c, d} : Finset V) ∩ s).card = 2 := by
    have heq : ({b, c, d} : Finset V) ∩ s = {b, c} := by
      rw [hs_eq]
      ext x
      simp only [mem_inter, mem_insert, mem_singleton]
      aesop
    rw [heq]
    simp [hbc]
  have hr_inter_t : (({b, c, d} : Finset V) ∩ t).card = 2 := by
    have heq : ({b, c, d} : Finset V) ∩ t = {b, d} := by
      rw [ht_eq]
      ext x
      simp only [mem_inter, mem_insert, mem_singleton]
      aesop
    rw [heq]
    simp [hbd]
  have hr_inter_u : (({b, c, d} : Finset V) ∩ u).card = 2 := by
    have heq : ({b, c, d} : Finset V) ∩ u = {c, d} := by
      rw [hu_eq]
      ext x
      simp only [mem_inter, mem_insert, mem_singleton]
      aesop
    rw [heq]
    simp [hcd]
  have hunion_card : (s ∪ t ∪ u).card = 4 := by
    have heq : s ∪ t ∪ u = {a, b, c, d} := by
      rw [hs_eq, ht_eq, hu_eq]
      ext x
      simp only [mem_union, mem_insert, mem_singleton]
      aesop
    rw [heq]
    simp [hab, hac, had, hbc, hbd, hcd]
  exact ⟨{b, c, d}, hr_nclique, hr_ne_s, hr_ne_t, hr_ne_u,
         hr_inter_s, hr_inter_t, hr_inter_u, hunion_card⟩
