import AFTD.Prelude
import AFTD.Kb.Tcs.TreeCardFourDegreeTwoCount

/-!
# tree_card_four_path_edges

Topic: graphs   Node: 32e9d4fb8dee

Provenance: helper lemma. step towards tree_card_four_iso_of_degree_le_two

Any tree on 4 vertices with all degrees at most 2 has an ordering (a, b, c, d) of its 4 vertices such that edges are precisely (a,b), (b,c), (c,d).
-/

/-- Any tree on 4 vertices with all degrees at most 2 has its 4 vertices orderable as a, b, c, d such that the edges are precisely (a, b), (b, c), and (c, d). -/
theorem tree_card_four_path_edges {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : Fintype.card V = 4)
    (hdeg : ∀ v : V, T.degree v ≤ 2) :
    ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      (∀ x : V, x = a ∨ x = b ∨ x = c ∨ x = d) ∧
      (∀ x y : V, T.Adj x y ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨
                              (x = b ∧ y = c) ∨ (x = c ∧ y = b) ∨
                              (x = c ∧ y = d) ∨ (x = d ∧ y = c)) := by
  have h_ne_zero : ∀ u : V, T.degree u ≠ 0 := by
    intro u h0
    have _ : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have h_iso : ¬ T.IsIsolated u := hT.connected.preconnected.not_isIsolated u
    rw [SimpleGraph.degree_eq_zero] at h0
    exact h_iso h0
  have hdeg_cases : ∀ v : V, T.degree v = 1 ∨ T.degree v = 2 := by
    intro v
    have h1 := hdeg v
    have h2 := h_ne_zero v
    omega
  have h_counts := tree_card_four_degree_two_count T hT hcard hdeg
  have hs2_card : (Finset.univ.filter (fun v => T.degree v = 2)).card = 2 := h_counts.1
  have hs1_card : (Finset.univ.filter (fun v => T.degree v = 1)).card = 2 := h_counts.2
  rcases Finset.card_eq_two.mp hs2_card with ⟨b, c, hbc, heq2⟩
  have hb2 : T.degree b = 2 := by
    have : b ∈ ({b, c} : Finset V) := by simp
    rw [← heq2] at this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  have hc2 : T.degree c = 2 := by
    have : c ∈ ({b, c} : Finset V) := by simp
    rw [← heq2] at this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  have hall2 : ∀ v : V, T.degree v = 2 → v = b ∨ v = c := by
    intro v hv
    have : v ∈ Finset.univ.filter (fun u => T.degree u = 2) := by simp [hv]
    rw [heq2] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact this
  have hbc_adj : T.Adj b c := by
    by_contra hnot
    have h_nb_sub : T.neighborFinset b ⊆ Finset.univ.filter (fun v => T.degree v = 1) := by
      intro x hx
      simp only [T.mem_neighborFinset] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hxb : x ≠ b := (T.ne_of_adj hx).symm
      have hxc : x ≠ c := by
        rintro rfl
        exact hnot hx
      cases hdeg_cases x with
      | inl h1 => exact h1
      | inr h2 =>
        cases hall2 x h2 with
        | inl heq => exact (hxb heq).elim
        | inr heq => exact (hxc heq).elim
    have h_card_nb : (T.neighborFinset b).card = 2 := by
      rw [T.card_neighborFinset_eq_degree, hb2]
    have h_eq_b : T.neighborFinset b = Finset.univ.filter (fun v => T.degree v = 1) :=
      Finset.eq_of_subset_of_card_le h_nb_sub (by rw [h_card_nb, hs1_card])
    have h_nc_sub : T.neighborFinset c ⊆ Finset.univ.filter (fun v => T.degree v = 1) := by
      intro x hx
      simp only [T.mem_neighborFinset] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hxc : x ≠ c := (T.ne_of_adj hx).symm
      have hxb : x ≠ b := by
        rintro rfl
        exact hnot hx.symm
      cases hdeg_cases x with
      | inl h1 => exact h1
      | inr h2 =>
        cases hall2 x h2 with
        | inl heq => exact (hxb heq).elim
        | inr heq => exact (hxc heq).elim
    have h_card_nc : (T.neighborFinset c).card = 2 := by
      rw [T.card_neighborFinset_eq_degree, hc2]
    have h_eq_c : T.neighborFinset c = Finset.univ.filter (fun v => T.degree v = 1) :=
      Finset.eq_of_subset_of_card_le h_nc_sub (by rw [h_card_nc, hs1_card])
    have h_nonempty : (Finset.univ.filter (fun v => T.degree v = 1)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := h_nonempty
    have hx1 : T.degree x = 1 := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx
    have hxb_adj : T.Adj b x := by
      have : x ∈ T.neighborFinset b := by rw [h_eq_b]; exact hx
      rwa [T.mem_neighborFinset] at this
    have hxc_adj : T.Adj c x := by
      have : x ∈ T.neighborFinset c := by rw [h_eq_c]; exact hx
      rwa [T.mem_neighborFinset] at this
    have h_sub : {b, c} ⊆ T.neighborFinset x := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · rw [T.mem_neighborFinset]
        exact hxb_adj.symm
      · rw [T.mem_neighborFinset]
        exact hxc_adj.symm
    have h_card_le : ({b, c} : Finset V).card ≤ (T.neighborFinset x).card :=
      Finset.card_le_card h_sub
    rw [Finset.card_pair hbc, T.card_neighborFinset_eq_degree, hx1] at h_card_le
    omega
  have hc_in_nb : c ∈ T.neighborFinset b := by rwa [T.mem_neighborFinset]
  have hb_in_nc : b ∈ T.neighborFinset c := by rwa [T.mem_neighborFinset, SimpleGraph.adj_comm]
  have h_card_nb_erase : ((T.neighborFinset b).erase c).card = 1 := by
    rw [Finset.card_erase_of_mem hc_in_nb, T.card_neighborFinset_eq_degree, hb2]
  have h_card_nc_erase : ((T.neighborFinset c).erase b).card = 1 := by
    rw [Finset.card_erase_of_mem hb_in_nc, T.card_neighborFinset_eq_degree, hc2]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_card_nb_erase
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp h_card_nc_erase
  have ha_in : a ∈ (T.neighborFinset b).erase c := by rw [ha]; exact Finset.mem_singleton_self a
  have hd_in : d ∈ (T.neighborFinset c).erase b := by rw [hd]; exact Finset.mem_singleton_self d
  rw [Finset.mem_erase, T.mem_neighborFinset] at ha_in hd_in
  have hac : a ≠ c := ha_in.1
  have hab_adj : T.Adj b a := ha_in.2
  have hab : a ≠ b := (T.ne_of_adj hab_adj).symm
  have hdb : d ≠ b := hd_in.1
  have hbd : b ≠ d := hdb.symm
  have hcd_adj : T.Adj c d := hd_in.2
  have hcd : c ≠ d := (T.ne_of_adj hcd_adj)
  have h_deg_a : T.degree a = 1 := by
    cases hdeg_cases a with
    | inl h1 => exact h1
    | inr h2 =>
      cases hall2 a h2 with
      | inl h => exact (hab h).elim
      | inr h => exact (hac h).elim
  have h_deg_d : T.degree d = 1 := by
    cases hdeg_cases d with
    | inl h1 => exact h1
    | inr h2 =>
      cases hall2 d h2 with
      | inl h => exact (hbd.symm h).elim
      | inr h => exact (hcd h.symm).elim
  have had : a ≠ d := by
    rintro rfl
    have h_sub : {b, c} ⊆ T.neighborFinset a := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · rw [T.mem_neighborFinset]
        exact hab_adj.symm
      · rw [T.mem_neighborFinset]
        exact hcd_adj.symm
    have h_card_le := Finset.card_le_card h_sub
    rw [Finset.card_pair hbc, T.card_neighborFinset_eq_degree, h_deg_a] at h_card_le
    omega
  have h_nb : T.neighborFinset b = {a, c} := by
    ext v
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hv
      by_cases hvc : v = c
      · exact Or.inr hvc
      · have : v ∈ (T.neighborFinset b).erase c := by
          rw [Finset.mem_erase]
          exact ⟨hvc, hv⟩
        rw [ha, Finset.mem_singleton] at this
        exact Or.inl this
    · rintro (rfl | rfl)
      · rwa [T.mem_neighborFinset]
      · exact hc_in_nb
  have h_nc : T.neighborFinset c = {b, d} := by
    ext v
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hv
      by_cases hvb : v = b
      · exact Or.inl hvb
      · have : v ∈ (T.neighborFinset c).erase b := by
          rw [Finset.mem_erase]
          exact ⟨hvb, hv⟩
        rw [hd, Finset.mem_singleton] at this
        exact Or.inr this
    · rintro (rfl | rfl)
      · exact hb_in_nc
      · rwa [T.mem_neighborFinset]
  have h_na : T.neighborFinset a = {b} := by
    have h_sub : {b} ⊆ T.neighborFinset a := by
      rw [Finset.singleton_subset_iff, T.mem_neighborFinset]
      exact hab_adj.symm
    have heq := Finset.eq_of_subset_of_card_le h_sub (by
      rw [Finset.card_singleton, T.card_neighborFinset_eq_degree, h_deg_a])
    exact heq.symm
  have h_nd : T.neighborFinset d = {c} := by
    have h_sub : {c} ⊆ T.neighborFinset d := by
      rw [Finset.singleton_subset_iff, T.mem_neighborFinset]
      exact hcd_adj.symm
    have heq := Finset.eq_of_subset_of_card_le h_sub (by
      rw [Finset.card_singleton, T.card_neighborFinset_eq_degree, h_deg_d])
    exact heq.symm
  have h_univ : ∀ x : V, x = a ∨ x = b ∨ x = c ∨ x = d := by
    intro x
    have h4 : ({a, b, c, d} : Finset V).card = 4 := by
      simp [hab, hac, had, hbc, hbd, hcd]
    have h_univ_eq : ({a, b, c, d} : Finset V) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [h4, hcard]
    have hx : x ∈ ({a, b, c, d} : Finset V) := by
      rw [h_univ_eq]
      exact Finset.mem_univ x
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    exact hx
  have h_adj_iff : ∀ x y : V, T.Adj x y ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨
                                         (x = b ∧ y = c) ∨ (x = c ∧ y = b) ∨
                                         (x = c ∧ y = d) ∨ (x = d ∧ y = c) := by
    intro x y
    constructor
    · intro h
      cases h_univ x with
      | inl hxa =>
        rw [hxa] at h ⊢
        have hy : y ∈ T.neighborFinset a := by rwa [T.mem_neighborFinset]
        rw [h_na, Finset.mem_singleton] at hy
        exact Or.inl ⟨rfl, hy⟩
      | inr hx =>
        cases hx with
        | inl hxb =>
          rw [hxb] at h ⊢
          have hy : y ∈ T.neighborFinset b := by rwa [T.mem_neighborFinset]
          rw [h_nb, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        | inr hx =>
          cases hx with
          | inl hxc =>
            rw [hxc] at h ⊢
            have hy : y ∈ T.neighborFinset c := by rwa [T.mem_neighborFinset]
            rw [h_nc, Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
          | inr hxd =>
            rw [hxd] at h ⊢
            have hy : y ∈ T.neighborFinset d := by rwa [T.mem_neighborFinset]
            rw [h_nd, Finset.mem_singleton] at hy
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hy⟩))))
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · rw [h1, h2, ← T.mem_neighborFinset, h_na]
        exact Finset.mem_singleton_self b
      · rw [h1, h2, ← T.mem_neighborFinset, h_nb]
        exact Finset.mem_insert_self a {c}
      · rw [h1, h2, ← T.mem_neighborFinset, h_nb]
        simp
      · rw [h1, h2, ← T.mem_neighborFinset, h_nc]
        exact Finset.mem_insert_self b {d}
      · rw [h1, h2, ← T.mem_neighborFinset, h_nc]
        simp
      · rw [h1, h2, ← T.mem_neighborFinset, h_nd]
        exact Finset.mem_singleton_self c
  exact ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, h_univ, h_adj_iff⟩
