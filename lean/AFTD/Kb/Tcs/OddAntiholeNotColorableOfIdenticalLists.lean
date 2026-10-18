import AFTD.Prelude

/-!
# odd_antihole_not_colorable_of_identical_lists

Topic: graphs   Node: f92283f88045

Provenance: helper lemma. arXiv:2610.14241 (Restricting odd antiholes in critical graphs via list coloring), Sec. 2, remark after Theorem 8 (identical lists of size ℓ-1 are an obstruction for an ℓ-chromatic graph); partial result for OP-216

For ℓ ≥ 3, the odd antihole complement(C_{2ℓ-1}) has no proper coloring from identical lists of size ℓ-1: the exception in strong ℓ-chromatic-choosability is necessary.
-/

/-- In a cycle graph on `m + 2 ≥ 2` vertices, adjacency means being a cyclic successor of one another. -/
theorem odd_antihole_not_colorable_of_identical_lists_adj_iff_add_one
    {m : ℕ} {a b : Fin (m + 2)} :
    (SimpleGraph.cycleGraph (m + 2)).Adj a b ↔ b = a + 1 ∨ a = b + 1 := by
  rw [SimpleGraph.cycleGraph_adj]
  constructor
  · rintro (h | h)
    · exact Or.inr ((sub_eq_iff_eq_add.mp h).trans (add_comm _ _))
    · exact Or.inl ((sub_eq_iff_eq_add.mp h).trans (add_comm _ _))
  · rintro (h | h)
    · exact Or.inr (sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _)))
    · exact Or.inl (sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _)))

/-- Value form of "`y` is the cyclic successor of `x`" in `Fin (m + 2)`. -/
theorem odd_antihole_not_colorable_of_identical_lists_succ_val
    {m : ℕ} {x y : Fin (m + 2)} (h : y = x + 1) :
    y.val = x.val + 1 ∨ (y.val = 0 ∧ x.val = m + 1) := by
  have hv : y.val = (x.val + 1) % (m + 2) := by rw [h, Fin.val_add]; simp
  have hx : x.val < m + 2 := x.isLt
  rcases Nat.lt_or_ge (x.val + 1) (m + 2) with hlt | hge
  · left; rw [Nat.mod_eq_of_lt hlt] at hv; exact hv
  · right
    have h1 : x.val + 1 = m + 2 := by omega
    exact ⟨by rw [hv, h1, Nat.mod_self], by omega⟩

/-- Adjacency in a cycle graph expressed as linear facts about `Fin.val`. -/
theorem odd_antihole_not_colorable_of_identical_lists_adj_val
    {m : ℕ} {a b : Fin (m + 2)} (h : (SimpleGraph.cycleGraph (m + 2)).Adj a b) :
    b.val = a.val + 1 ∨ (b.val = 0 ∧ a.val = m + 1) ∨
      a.val = b.val + 1 ∨ (a.val = 0 ∧ b.val = m + 1) := by
  rw [odd_antihole_not_colorable_of_identical_lists_adj_iff_add_one] at h
  rcases h with h | h
  · rcases odd_antihole_not_colorable_of_identical_lists_succ_val h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases odd_antihole_not_colorable_of_identical_lists_succ_val h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))

/-- A cycle graph of length at least `5` contains no triangle. -/
theorem odd_antihole_not_colorable_of_identical_lists_triple
    {N : ℕ} (hN : 5 ≤ N) {a b c : Fin N}
    (hab : (SimpleGraph.cycleGraph N).Adj a b)
    (hac : (SimpleGraph.cycleGraph N).Adj a c)
    (hbc : (SimpleGraph.cycleGraph N).Adj b c) : a = b ∨ a = c ∨ b = c := by
  by_contra h
  push Not at h
  obtain ⟨habne, hacne, hbcne⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have h1 := odd_antihole_not_colorable_of_identical_lists_adj_val hab
  have h2 := odd_antihole_not_colorable_of_identical_lists_adj_val hac
  have h3 := odd_antihole_not_colorable_of_identical_lists_adj_val hbc
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [Fin.ext_iff, ne_eq] at habne hacne hbcne
  omega

/-- Every clique of a cycle graph on at least `5` vertices has at most two vertices. -/
theorem odd_antihole_not_colorable_of_identical_lists_clique_card_le_two
    {N : ℕ} (hN : 5 ≤ N) (t : Finset (Fin N))
    (h : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → (SimpleGraph.cycleGraph N).Adj u v) : t.card ≤ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ := Finset.two_lt_card (s := t) |>.mp hcon
  rcases odd_antihole_not_colorable_of_identical_lists_triple hN
      (h u hu v hv huv) (h u hu w hw huw) (h v hv w hw hvw) with h' | h' | h'
  · exact huv h'
  · exact huw h'
  · exact hvw h'

theorem odd_antihole_not_colorable_of_identical_lists (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (S : Finset ℕ)
    (hS : S.card = ℓ - 1) :
    ¬ ∃ c : Fin (2 * ℓ - 1) → ℕ, (∀ v, c v ∈ S) ∧
      ∀ u v, (SimpleGraph.cycleGraph (2 * ℓ - 1))ᶜ.Adj u v → c u ≠ c v := by
  rintro ⟨c, hcS, hproper⟩
  have hN : 5 ≤ 2 * ℓ - 1 := by omega
  have hadj : ∀ u v : Fin (2 * ℓ - 1), u ≠ v → c u = c v →
      (SimpleGraph.cycleGraph (2 * ℓ - 1)).Adj u v := by
    intro u v huv heq
    by_contra hnot
    exact hproper u v ((SimpleGraph.compl_adj _ u v).mpr ⟨huv, hnot⟩) heq
  have hbound : ∀ s ∈ S, (Finset.univ.filter (fun v => c v = s)).card ≤ 2 := by
    intro s hs
    apply odd_antihole_not_colorable_of_identical_lists_clique_card_le_two hN
    intro u hu v hv huv
    simp only [Finset.mem_filter] at hu hv
    exact hadj u v huv (hu.2.trans hv.2.symm)
  have himg : Finset.image c (Finset.univ : Finset (Fin (2 * ℓ - 1))) ⊆ S := by
    intro s hs
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hs
    exact hcS v
  have hle : (Finset.univ : Finset (Fin (2 * ℓ - 1))).card ≤
      2 * (Finset.image c (Finset.univ : Finset (Fin (2 * ℓ - 1)))).card :=
    Finset.card_le_mul_card_image (Finset.univ : Finset (Fin (2 * ℓ - 1))) 2 (by
      intro b hb
      exact hbound b (himg hb))
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  have h2 : (Finset.image c (Finset.univ : Finset (Fin (2 * ℓ - 1)))).card ≤ S.card :=
    Finset.card_le_card himg
  omega
