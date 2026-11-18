import AFTD.Prelude
import AFTD.Kb.Tcs.Op861UnbalancedSelectorsHypergraphIff

/-!
# op861_palette_surplus_hypergraph_iff

Topic: graphs   Node: 73e40381be56

Provenance: helper lemma. Palette-surplus reduction for the open problem OP-861; finite models checked in experiment 30660.

A standard-list coloring whose first selector stays in a prescribed k+r+s-color palette exists exactly when the specified uniform hypergraph coverage and avoidance conditions hold on that palette.
-/

theorem op861_palette_surplus_hypergraph_iff (k r s : ℕ) (hsmall : r + s < k)
    (U : Finset (Fin (2*k - 1))) (hU : U.card = k + r + s) :
    (∃ f g : {S : Finset (Fin (2*k - 1)) // S.card = k} → Fin (2*k - 1),
      (∀ S, f S ∈ S.1 ∧ f S ∈ U) ∧ (∀ T, g T ∈ T.1) ∧
      ∀ S T, (S.1 ∩ T.1).card ≤ r → f S ≠ g T) ↔
    ∃ H : Fin (2*k - 1) → Finset (Fin (2*k - 1)) → Prop,
      (∀ v Y, H v Y → v ∈ U ∧ Y ⊆ U ∧ Y.card = s + 1 ∧ v ∉ Y) ∧
      (∀ X : Finset (Fin (2*k - 1)), X ⊆ U → X.card = r + s + 1 →
        ∃ v ∈ X, ∀ Y : Finset (Fin (2*k - 1)),
          Y ⊆ X.erase v → Y.card = s + 1 → H v Y) ∧
      (∀ R : Finset (Fin (2*k - 1)), R ⊆ U → R.card = r + s →
        ∃ v ∈ U, v ∉ R ∧ ∀ Y : Finset (Fin (2*k - 1)), H v Y → ¬ Y ⊆ R) := by
  constructor
  · rintro ⟨f, g, hf, hg, hproper⟩
    classical
    let C : Finset (Fin (2*k - 1)) := Finset.univ \ U
    have h_univ : (Finset.univ : Finset (Fin (2*k - 1))).card = 2 * k - 1 := by simp
    have hC_card : C.card = k - r - s - 1 := by
      dsimp [C]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), h_univ, hU]
      omega
    have hCX_card : ∀ X ⊆ U, X.card = r + s + 1 → (C ∪ X).card = k := by
      intro X hXU hX
      have hdisj : Disjoint C X := by
        rw [Finset.disjoint_left]
        intro x hxC hxX
        exact (Finset.mem_sdiff.mp hxC).2 (hXU hxX)
      rw [Finset.card_union_of_disjoint hdisj, hC_card, hX]
      omega
    let H : Fin (2*k - 1) → Finset (Fin (2*k - 1)) → Prop := fun v Y =>
      v ∈ U ∧ Y ⊆ U ∧ Y.card = s + 1 ∧ v ∉ Y ∧
        ∃ (X : Finset (Fin (2*k - 1))) (hXU : X ⊆ U) (hXcard : X.card = r + s + 1),
          f ⟨C ∪ X, hCX_card X hXU hXcard⟩ = v ∧ Y ⊆ X.erase v
    refine ⟨H, ?_, ?_, ?_⟩
    · intro v Y h
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
    · intro X hXU hXcard
      have hcard := hCX_card X hXU hXcard
      let v := f ⟨C ∪ X, hcard⟩
      have hv_in := (hf ⟨C ∪ X, hcard⟩).1
      have hv_U := (hf ⟨C ∪ X, hcard⟩).2
      have hv_X : v ∈ X := by
        rcases Finset.mem_union.mp hv_in with hvC | hvX
        · exact False.elim ((Finset.mem_sdiff.mp hvC).2 hv_U)
        · exact hvX
      refine ⟨v, hv_X, ?_⟩
      intro Y hYX hYcard
      refine ⟨hv_U, ?_, hYcard, ?_, X, hXU, hXcard, rfl, hYX⟩
      · exact hYX.trans ((Finset.erase_subset v X).trans hXU)
      · intro hvY
        exact (Finset.mem_erase.mp (hYX hvY)).1 rfl
    · intro R hRU hRcard
      let T : Finset (Fin (2*k - 1)) := U \ R
      have hTcard : T.card = k := by
        have hTsub : R ⊆ U := hRU
        have hsdiff := Finset.card_sdiff_of_subset hTsub
        dsimp [T]
        rw [hsdiff, hU, hRcard]
        omega
      let t : {T : Finset (Fin (2*k - 1)) // T.card = k} := ⟨T, hTcard⟩
      let v := g t
      have hvT : v ∈ T := hg t
      have hvU : v ∈ U := (Finset.mem_sdiff.mp hvT).1
      have hvR : v ∉ R := (Finset.mem_sdiff.mp hvT).2
      refine ⟨v, hvU, hvR, ?_⟩
      intro Y hH hYR
      obtain ⟨-, -, hYcard, -, X, hXU, hXcard, hfX, hYX⟩ := hH
      let S := C ∪ X
      have hcardS := hCX_card X hXU hXcard
      have hproper_app := hproper ⟨S, hcardS⟩ t
      have hST : (S ∩ T).card ≤ r := by
        have hCT_disj : Disjoint C T := by
          rw [Finset.disjoint_left]
          intro x hxC hxT
          exact (Finset.mem_sdiff.mp hxC).2 (Finset.mem_sdiff.mp hxT).1
        have hST_eq : S ∩ T = X ∩ T := by
          dsimp [S]
          rw [Finset.union_inter_distrib_right, (Finset.disjoint_iff_inter_eq_empty.mp hCT_disj), Finset.empty_union]
        rw [hST_eq]
        have hXT_eq : X ∩ T = X \ R := by
          ext x
          simp only [T, Finset.mem_inter, Finset.mem_sdiff]
          constructor
          · rintro ⟨hxX, hxU, hxR⟩; exact ⟨hxX, hxR⟩
          · rintro ⟨hxX, hxR⟩; exact ⟨hxX, hXU hxX, hxR⟩
        rw [hXT_eq]
        have hdisj : Disjoint Y (X \ R) := by
          rw [Finset.disjoint_left]
          intro x hxY hxXR
          exact (Finset.mem_sdiff.mp hxXR).2 (hYR hxY)
        have hsub : Y ∪ (X \ R) ⊆ X := by
          apply Finset.union_subset
          · exact hYX.trans (Finset.erase_subset v X)
          · exact Finset.sdiff_subset
        have hcard_le := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, hYcard, hXcard] at hcard_le
        omega
      apply hproper_app hST
      exact hfX.trans (rfl : v = g t)
  · rintro ⟨H, _hHprop, hcover, havoid⟩
    classical
    let C : Finset (Fin (2*k - 1)) := Finset.univ \ U
    have h_univ : (Finset.univ : Finset (Fin (2*k - 1))).card = 2 * k - 1 := by simp
    have hC_card : C.card = k - r - s - 1 := by
      dsimp [C]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), h_univ, hU]
      omega
    have h_choice_S : ∀ S : {S : Finset (Fin (2*k - 1)) // S.card = k},
        ∃ v ∈ S.1 ∩ U, ∃ X ⊆ S.1 ∩ U, X.card = r + s + 1 ∧ v ∈ X ∧
          ∀ Y ⊆ X.erase v, Y.card = s + 1 → H v Y := by
      intro S
      have hS_sub : S.1 \ U ⊆ C := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
      have hS_diff_le : (S.1 \ U).card ≤ C.card := Finset.card_le_card hS_sub
      have h_split : S.1.card = (S.1 ∩ U).card + (S.1 \ U).card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext x
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
          tauto
        · rw [Finset.disjoint_left]
          intro x hx1 hx2
          exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_inter.mp hx1).2
      have hScard := S.2
      have hcard_ge : r + s + 1 ≤ (S.1 ∩ U).card := by omega
      obtain ⟨X, hX_sub, hX_card⟩ := Finset.exists_subset_card_eq hcard_ge
      have hX_U : X ⊆ U := hX_sub.trans Finset.inter_subset_right
      obtain ⟨v, hvX, hH_cov⟩ := hcover X hX_U hX_card
      refine ⟨v, hX_sub hvX, X, hX_sub, hX_card, hvX, hH_cov⟩
    let f : {S : Finset (Fin (2*k - 1)) // S.card = k} → Fin (2*k - 1) :=
      fun S => Classical.choose (h_choice_S S)
    have hf_spec (S : {S : Finset (Fin (2*k - 1)) // S.card = k}) :
        f S ∈ S.1 ∩ U ∧ ∃ X ⊆ S.1 ∩ U, X.card = r + s + 1 ∧ f S ∈ X ∧
          ∀ Y ⊆ X.erase (f S), Y.card = s + 1 → H (f S) Y :=
      Classical.choose_spec (h_choice_S S)
    have h_choice_T : ∀ T : {T : Finset (Fin (2*k - 1)) // T.card = k},
        ∃ v ∈ T.1, (v ∉ U) ∨ (∀ Y, H v Y → ¬ Y ⊆ U \ T.1) := by
      intro T
      by_cases hne : (T.1 \ U).Nonempty
      · obtain ⟨v, hv⟩ := hne
        exact ⟨v, (Finset.mem_sdiff.mp hv).1, Or.inl (Finset.mem_sdiff.mp hv).2⟩
      · rw [Finset.nonempty_iff_ne_empty, not_not, Finset.sdiff_eq_empty_iff_subset] at hne
        let R := U \ T.1
        have hRcard : R.card = r + s := by
          dsimp [R]
          rw [Finset.card_sdiff_of_subset hne, hU, T.2]
          omega
        have hRU : R ⊆ U := Finset.sdiff_subset
        obtain ⟨v, hvU, hvR, hHav⟩ := havoid R hRU hRcard
        have hvT : v ∈ T.1 := by
          by_contra hnot
          exact hvR (Finset.mem_sdiff.mpr ⟨hvU, hnot⟩)
        exact ⟨v, hvT, Or.inr hHav⟩
    let g : {T : Finset (Fin (2*k - 1)) // T.card = k} → Fin (2*k - 1) :=
      fun T => Classical.choose (h_choice_T T)
    have hg_spec (T : {T : Finset (Fin (2*k - 1)) // T.card = k}) :
        g T ∈ T.1 ∧ ((g T ∉ U) ∨ (∀ Y, H (g T) Y → ¬ Y ⊆ U \ T.1)) :=
      Classical.choose_spec (h_choice_T T)
    refine ⟨f, g, ?_, ?_, ?_⟩
    · intro S
      exact ⟨(Finset.mem_inter.mp (hf_spec S).1).1, (Finset.mem_inter.mp (hf_spec S).1).2⟩
    · intro T
      exact (hg_spec T).1
    · intro S T hint heq
      have hvU : f S ∈ U := (Finset.mem_inter.mp (hf_spec S).1).2
      have hg_disj := (hg_spec T).2
      rw [← heq] at hg_disj
      rcases hg_disj with hnotU | hHav
      · exact hnotU hvU
      · obtain ⟨-, X, hX_sub, hX_card, hvX, hH_cov⟩ := hf_spec S
        have hX_S : X ⊆ S.1 := hX_sub.trans Finset.inter_subset_left
        have hX_U : X ⊆ U := hX_sub.trans Finset.inter_subset_right
        let W := X \ T.1
        have h_split : X.card = (X \ T.1).card + (X ∩ T.1).card := by
          rw [← Finset.card_union_of_disjoint]
          · congr 1
            ext x
            simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
            tauto
          · rw [Finset.disjoint_left]
            intro x hx1 hx2
            exact (Finset.mem_sdiff.mp hx1).2 (Finset.mem_inter.mp hx2).2
        have hXT_sub : X ∩ T.1 ⊆ S.1 ∩ T.1 := Finset.inter_subset_inter_right hX_S
        have hXT_le : (X ∩ T.1).card ≤ r := (Finset.card_le_card hXT_sub).trans hint
        have hW_card : s + 1 ≤ W.card := by
          dsimp [W]
          omega
        obtain ⟨Y, hYW, hYcard⟩ := Finset.exists_subset_card_eq hW_card
        have hY_erase : Y ⊆ X.erase (f S) := by
          intro y hy
          have hyW := hYW hy
          have hyX := (Finset.mem_sdiff.mp hyW).1
          have hnotT := (Finset.mem_sdiff.mp hyW).2
          apply Finset.mem_erase.mpr
          refine ⟨?_, hyX⟩
          intro hy_eq
          apply hnotT
          rw [hy_eq, heq]
          exact (hg_spec T).1
        have hHY : H (f S) Y := hH_cov Y hY_erase hYcard
        have hYR : Y ⊆ U \ T.1 := by
          intro y hy
          have hyW := hYW hy
          have hyX := (Finset.mem_sdiff.mp hyW).1
          have hnotT := (Finset.mem_sdiff.mp hyW).2
          exact Finset.mem_sdiff.mpr ⟨hX_U hyX, hnotT⟩
        exact hHav Y hHY hYR
