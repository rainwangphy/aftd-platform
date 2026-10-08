import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonListColorable

/-!
# matroid_common_list_colorable_of_ncard_le

Topic: combinatorics   Node: 48171dc249b9

Provenance: helper lemma. Helper for the questions of arXiv:2610.07318 (Questions 3.1 and 3.2): it shows the set defining matroid_common_list_chromatic_number is nonempty for finite loopless pairs. Hint: choose distinct representatives with Hall's theorem (Finset.all_card_le_biUnion_card_iff_exists_injective) or greedily.

Two loopless matroids on a common finite ground set E are k-list-colorable whenever k ≥ |E|: from lists of at least |E| colors one can pick pairwise distinct colors, and then every color class has at most one element, which is independent in both matroids because they are loopless. In particular the common list chromatic number of such a pair is well defined.
-/

theorem matroid_common_list_colorable_of_ncard_le {α : Type*} (M₁ M₂ : Matroid α)
    [M₁.Finite] (h₁ : M₁.Loopless) (h₂ : M₂.Loopless) (hE : M₁.E = M₂.E) (k : ℕ)
    (hk : M₁.E.ncard ≤ k) : matroid_common_list_colorable M₁ M₂ k := by
  classical
  intro L hL
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun e : M₁.E => L e)).1 (by
      intro s
      rcases s.eq_empty_or_nonempty with rfl | ⟨e, he⟩
      · simp
      · have : Finite M₁.E := M₁.ground_finite.to_subtype
        have hs : s.card ≤ M₁.E.ncard := by
          rw [← Nat.card_coe_set_eq]
          have := Fintype.ofFinite M₁.E
          rw [Nat.card_eq_fintype_card]
          exact Finset.card_le_univ s
        calc s.card ≤ k := hs.trans hk
          _ ≤ (L e).card := hL e e.2
          _ ≤ (s.biUnion fun e : M₁.E => L e).card :=
            Finset.card_le_card (Finset.subset_biUnion_of_mem (fun e : M₁.E => L e) he))
  set c : α → ℕ := fun e => if he : e ∈ M₁.E then f ⟨e, he⟩ else 0 with hc
  -- every color class has at most one element, and single elements are independent
  have hsing : ∀ (M : Matroid α), M.Loopless → M.E = M₁.E → ∀ γ : ℕ,
      M.Indep {e | e ∈ M₁.E ∧ c e = γ} := by
    intro M hM hME γ
    have hsub : {e | e ∈ M₁.E ∧ c e = γ}.Subsingleton := by
      rintro a ⟨ha, haγ⟩ b ⟨hb, hbγ⟩
      have : f ⟨a, ha⟩ = f ⟨b, hb⟩ := by
        simp only [hc, dif_pos ha, dif_pos hb] at haγ hbγ
        rw [haγ, hbγ]
      exact congrArg Subtype.val (hfinj this)
    rcases hsub.eq_empty_or_singleton with h | ⟨e, h⟩
    · rw [h]; exact M.empty_indep
    · rw [h, Matroid.indep_singleton]
      have he : e ∈ M.E := by
        have : e ∈ {e | e ∈ M₁.E ∧ c e = γ} := h ▸ rfl
        exact hME ▸ this.1
      exact Matroid.isNonloop_of_loopless he
  refine ⟨c, fun e he => ?_, fun γ => ⟨hsing M₁ h₁ rfl γ, hsing M₂ h₂ hE.symm γ⟩⟩
  simp only [hc, dif_pos he]
  exact hf ⟨e, he⟩
