import AFTD.Prelude
import AFTD.Kb.Tcs.MixedRamseyProperty
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.HasMonochromaticFanCopy

/-!
# mixed_diamond_fan_ramsey_bound_all_singletons_one_fan_colour

Topic: combinatorics   Node: 707bc0d06e97

Provenance: helper lemma. step towards mixed_diamond_fan_ramsey_bound

Case b = 1 with every singleton of the unique fan colour: if d ≥ j*a + j and the statement holds at (a, 0) in dimension d-j, then χ has a monochromatic diamond in one of the a diamond colours or a monochromatic F_j in the single fan colour.
-/

/-- b = 1 step with the unique fan colour on every singleton: either a large fan-coloured set is already a fan, or every fan-coloured set has size < j and compressing onto a j-subset Y makes the colouring fan-free, so the (a, 0) instance at dimension d-j gives the diamond. -/
theorem mixed_diamond_fan_ramsey_bound_all_singletons_one_fan_colour (j a d : ℕ) (hj : 2 ≤ j)
    (ha : 1 ≤ a) (hd : j * a + j ≤ d)
    (ih : mixed_ramsey_property j a 0 (d - j))
    (χ : Finset (Fin d) → Fin (a + 1)) (hx : ∀ x : Fin d, χ {x} = Fin.natAdd a 0) :
    (∃ col : Fin a, has_monochromatic_diamond_copy j d (Fin.castAdd 1 col) χ) ∨
      ∃ col : Fin 1, has_monochromatic_fan_copy j d (Fin.natAdd a col) χ := by
  have hj_le_d : j ≤ d := by
    have : j * 1 + j ≤ j * a + j := by nlinarith
    omega
  by_cases h_fan : ∃ S : Finset (Fin d), j ≤ S.card ∧ χ S = Fin.natAdd a 0
  · right
    rcases h_fan with ⟨S, hS_card, hS_col⟩
    use 0
    unfold has_monochromatic_fan_copy
    refine ⟨S, hS_col, ?_⟩
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS_card
    have hT_equiv : Nonempty (Fin j ≃ T) := by
      have : Fintype.card T = j := by rw [Fintype.card_coe, hTcard]
      exact ⟨Fintype.equivFinOfCardEq this |>.symm⟩
    obtain ⟨e⟩ := hT_equiv
    let mid : Fin j → Finset (Fin d) := fun i => { (e i : Fin d) }
    refine ⟨mid, ?_, ?_⟩
    · intro i
      refine ⟨?_, hx (e i : Fin d)⟩
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.singleton_subset_iff.mpr (hTS (e i).2), ?_⟩
      intro heq
      have h1 : (mid i).card = S.card := congrArg Finset.card heq
      have h2 : (mid i).card = 1 := Finset.card_singleton _
      omega
    · intro i i' hne
      dsimp [mid]
      rw [Finset.singleton_subset_iff, Finset.mem_singleton]
      intro heq
      apply hne
      apply e.injective
      exact Subtype.ext heq
  · left
    have hd' : j + (d - j) = d := Nat.add_sub_of_le hj_le_d
    let e_iso := (Fin.castOrderIso hd').toEquiv
    let Y_emb : Fin j ↪ Fin d := (Fin.castAddEmb (d - j)).trans e_iso.toEmbedding
    let emb : Fin (d - j) ↪ Fin d := (Fin.natAddEmb j).trans e_iso.toEmbedding
    let Y : Finset (Fin d) := Finset.univ.map Y_emb
    have h_disj : ∀ x, emb x ∉ Y := by
      intro x
      rw [Finset.mem_map]
      rintro ⟨y, hy, heq⟩
      change e_iso (Fin.castAddEmb (d - j) y) = e_iso (Fin.natAddEmb j x) at heq
      have heq' := e_iso.injective heq
      have h_val := congrArg Fin.val heq'
      have h1 : (Fin.castAddEmb (d - j) y).val = y.val := rfl
      have h2 : (Fin.natAddEmb j x).val = j + x.val := rfl
      rw [h1, h2] at h_val
      have : y.val < j := y.isLt
      omega
    let U : Finset (Fin (d - j)) → Finset (Fin d) := fun B => B.map emb ∪ Y
    have hU_card : ∀ B, j ≤ (U B).card := by
      intro B
      have : Y ⊆ U B := Finset.subset_union_right
      have := Finset.card_le_card this
      have hY_card : Y.card = j := by
        rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
      omega
    have hU_sub : ∀ B B', U B ⊆ U B' ↔ B ⊆ B' := by
      intro B B'
      constructor
      · intro h x hx
        have h1 : emb x ∈ U B := by
          simp only [U, Finset.mem_union, Finset.mem_map]
          left; exact ⟨x, hx, rfl⟩
        have h2 := h h1
        simp only [U, Finset.mem_union, Finset.mem_map] at h2
        rcases h2 with ⟨y, hy, heqy⟩ | hy
        · have : y = x := emb.injective heqy
          rwa [← this]
        · exact (h_disj x hy).elim
      · intro h
        dsimp [U]
        exact Finset.union_subset_union_left (Finset.map_subset_map.mpr h)
    have hU_ssub : ∀ B B', U B ⊂ U B' ↔ B ⊂ B' := by
      intro B B'
      rw [Finset.ssubset_def, Finset.ssubset_def, hU_sub, hU_sub]
    have h_val_lt : ∀ B, (χ (U B)).val < a := by
      intro B
      have h_ne : χ (U B) ≠ Fin.natAdd a 0 := fun h => h_fan ⟨U B, hU_card B, h⟩
      have h1 : (Fin.natAdd a (0 : Fin 1)).val = a := rfl
      have h2 : (χ (U B)).val < a + 1 := (χ (U B)).isLt
      have h3 : (χ (U B)).val ≠ a := by
        intro h
        apply h_ne
        ext
        rw [h, h1]
      omega
    let ψ : Finset (Fin (d - j)) → Fin (a + 0) := fun B => ⟨(χ (U B)).val, by
      have := h_val_lt B
      omega⟩
    rcases ih ψ with ⟨col, hcol⟩ | ⟨col, _⟩
    · use col
      unfold has_monochromatic_diamond_copy at hcol ⊢
      rcases hcol with ⟨bot, top, h_bot_top, h_col_bot, h_col_top, mid, h_mid, h_incomp⟩
      refine ⟨U bot, U top, ?_, ?_, ?_, fun i => U (mid i), ?_, ?_⟩
      · rwa [hU_ssub]
      · ext
        have : (Fin.castAdd 0 col).val = col.val := rfl
        have : (Fin.castAdd 1 col).val = col.val := rfl
        have h_psi := congrArg Fin.val h_col_bot
        dsimp [ψ] at h_psi
        omega
      · ext
        have : (Fin.castAdd 0 col).val = col.val := rfl
        have : (Fin.castAdd 1 col).val = col.val := rfl
        have h_psi := congrArg Fin.val h_col_top
        dsimp [ψ] at h_psi
        omega
      · intro i
        refine ⟨?_, ?_, ?_⟩
        · rw [hU_ssub]
          exact (h_mid i).1
        · rw [hU_ssub]
          exact (h_mid i).2.1
        · dsimp only
          ext
          have : (Fin.castAdd 0 col).val = col.val := rfl
          have : (Fin.castAdd 1 col).val = col.val := rfl
          have h_psi := congrArg Fin.val (h_mid i).2.2
          dsimp [ψ] at h_psi
          omega
      · intro i i' hne
        rw [hU_sub]
        exact h_incomp i i' hne
    · exact col.elim0
