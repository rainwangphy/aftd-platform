import AFTD.Prelude
import AFTD.Kb.Tcs.GhzIsPerfectMatching

/-!
# ghz_matching_cross_cut_card_parity

Topic: quantum   Node: 00f617474955

Provenance: helper lemma. arXiv:2610.22190 Section 4

For any finite type V with decidable equality, simple graph G on V, perfect matching M of G, and subset S ⊆ V, the number of edges in M crossing the cut between S and Sᶜ has the same parity modulo 2 as the cardinality of S.
-/

/-- Parity of the number of edges in a perfect matching crossing a cut equals the cut parity. -/
lemma ghz_matching_cross_cut_card_parity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (M : Finset (Sym2 V)) (hM : ghz_is_perfect_matching G M)
    (S : Finset V) :
    (M.filter (fun e => ∃ u ∈ S, ∃ v ∈ (Sᶜ : Finset V), e = s(u, v))).card % 2 = S.card % 2 := by
  classical
  rw [ghz_is_perfect_matching] at hM
  obtain ⟨hmem, hcov⟩ := hM
  have huniq : ∀ v (e e' : Sym2 V), e ∈ M → v ∈ e → e' ∈ M → v ∈ e' → e = e' := by
    intro v e e' he hv he' hv'
    obtain ⟨e0, _he0, hu⟩ := hcov v
    exact (hu e ⟨he, hv⟩).trans (hu e' ⟨he', hv'⟩).symm
  have hdisj : (M : Set (Sym2 V)).PairwiseDisjoint (fun e => e.toFinset ∩ S) := by
    intro e he e' he' hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_inter, Sym2.mem_toFinset] at hv hv'
    exact hne (huniq v e e' he hv.1 he' hv'.1)
  have hS : S = M.biUnion (fun e => e.toFinset ∩ S) := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_inter, Sym2.mem_toFinset]
    constructor
    · intro hv
      obtain ⟨e, he, _⟩ := hcov v
      exact ⟨e, he.1, he.2, hv⟩
    · rintro ⟨e, he, hv1, hv2⟩
      exact hv2
  have hcard : S.card = ∑ e ∈ M, (e.toFinset ∩ S).card := by
    conv_lhs => rw [hS]
    exact Finset.card_biUnion hdisj
  have h_edge : ∀ e ∈ M, (((e.toFinset ∩ S).card : ZMod 2) =
      if (∃ u ∈ S, ∃ v ∈ (Sᶜ : Finset V), e = s(u, v)) then 1 else 0) := by
    intro e he
    have he_edge : e ∈ G.edgeSet := hmem e he
    induction' e using Sym2.inductionOn with u v
    rw [SimpleGraph.mem_edgeSet] at he_edge
    have hne : u ≠ v := he_edge.ne
    rw [Sym2.toFinset_mk_eq]
    have h_cond_iff : (∃ x ∈ S, ∃ y ∈ (Sᶜ : Finset V), s(u, v) = s(x, y)) ↔
        (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := by
      constructor
      · rintro ⟨x, hx, y, hy, hxy⟩
        rw [Finset.mem_compl] at hy
        rw [Sym2.eq_iff] at hxy
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hy⟩
      · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
        · exact ⟨u, hu, v, Finset.mem_compl.mpr hv, rfl⟩
        · exact ⟨v, hv, u, Finset.mem_compl.mpr hu, Sym2.eq_swap⟩
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · have hcond : ¬ (∃ x ∈ S, ∃ y ∈ (Sᶜ : Finset V), s(u, v) = s(x, y)) := by
        rw [h_cond_iff]; tauto
      rw [if_neg hcond]
      have hinter : ({u, v} : Finset V) ∩ S = {u, v} := by ext x; simp [hu, hv]
      rw [hinter, Finset.card_pair hne]
      decide
    · have hcond : ∃ x ∈ S, ∃ y ∈ (Sᶜ : Finset V), s(u, v) = s(x, y) := by
        rw [h_cond_iff]; tauto
      rw [if_pos hcond]
      have hinter : ({u, v} : Finset V) ∩ S = {u} := by ext x; simp [hu, hv]
      rw [hinter, Finset.card_singleton]
      rfl
    · have hcond : ∃ x ∈ S, ∃ y ∈ (Sᶜ : Finset V), s(u, v) = s(x, y) := by
        rw [h_cond_iff]; tauto
      rw [if_pos hcond]
      have hinter : ({u, v} : Finset V) ∩ S = {v} := by ext x; simp [hu, hv]
      rw [hinter, Finset.card_singleton]
      rfl
    · have hcond : ¬ (∃ x ∈ S, ∃ y ∈ (Sᶜ : Finset V), s(u, v) = s(x, y)) := by
        rw [h_cond_iff]; tauto
      rw [if_neg hcond]
      have hinter : ({u, v} : Finset V) ∩ S = ∅ := by ext x; simp [hu, hv]
      rw [hinter, Finset.card_empty]
      rfl
  rw [← ZMod.natCast_eq_natCast_iff' _ _ 2]
  have h1 : (S.card : ZMod 2) = ∑ e ∈ M, ((e.toFinset ∩ S).card : ZMod 2) := by
    rw [hcard, Nat.cast_sum]
  have h2 : (∑ e ∈ M, ((e.toFinset ∩ S).card : ZMod 2)) =
      ∑ e ∈ M, (if (∃ u ∈ S, ∃ v ∈ (Sᶜ : Finset V), e = s(u, v)) then (1 : ZMod 2) else 0) := by
    apply Finset.sum_congr rfl
    intro e he
    exact h_edge e he
  have h3 : (∑ e ∈ M, (if (∃ u ∈ S, ∃ v ∈ (Sᶜ : Finset V), e = s(u, v)) then (1 : ZMod 2) else 0)) =
      (((M.filter (fun e => ∃ u ∈ S, ∃ v ∈ (Sᶜ : Finset V), e = s(u, v))).card : ℕ) : ZMod 2) := by
    rw [← Finset.sum_filter]
    simp
  rw [h1, h2, h3]
