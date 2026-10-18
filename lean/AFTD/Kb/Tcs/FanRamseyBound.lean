import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticFanCopy
import AFTD.Kb.Tcs.ExistsHittingSetOfNoLargeAntichain

/-!
# fan_ramsey_bound

Topic: combinatorics   Node: 6695309bf27b

Provenance: helper lemma. step towards diamond_poset_ramsey_number_le

For j ≥ 2 and k ≥ 1, every colouring of the subsets of Fin d with k colours, where d ≥ k(j-1)+1, contains a monochromatic induced copy of F_j (a maximum element over an antichain of size j).
-/

lemma fan_ramsey_bound_arith (j k d s : ℕ) (hk : 1 ≤ k) (hd : k * (j - 1) + 1 ≤ d) (hs : s ≤ j - 1) :
    (k - 1) * (j - 1) + 1 ≤ d - s := by
  have h1 : (k - 1) * (j - 1) + (j - 1) = k * (j - 1) := by
    calc (k - 1) * (j - 1) + (j - 1) = (k - 1) * (j - 1) + 1 * (j - 1) := by rw [one_mul]
      _ = ((k - 1) + 1) * (j - 1) := by rw [Nat.add_mul]
      _ = k * (j - 1) := by rw [Nat.sub_add_cancel hk]
  omega

lemma fan_ramsey_bound_base_one_gen (j : ℕ) {α : Type} [Fintype α] [DecidableEq α]
    (hj : 2 ≤ j) (hd : j ≤ Fintype.card α) (χ : Finset α → Fin 1) :
    ∃ col : Fin 1, ∃ top : Finset α, χ top = col ∧ ∃ mid : Fin j → Finset α,
      (∀ i, mid i ⊂ top ∧ χ (mid i) = col) ∧ ∀ i i', i ≠ i' → ¬ mid i ⊆ mid i' := by
  classical
  obtain ⟨T, -, hTcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset α)) (n := j) (by simpa using hd)
  let eT : ↥T ≃ Fin j := Finset.equivFinOfCardEq hTcard
  let a : Fin j → α := fun i => (eT.symm i).1
  have ha_mem : ∀ i, a i ∈ T := fun i => (eT.symm i).2
  have ha_inj : Function.Injective a := by
    intro i i' h
    exact eT.symm.injective (Subtype.ext h)
  let mid : Fin j → Finset α := fun i => T.erase (a i)
  have hmid_card : ∀ i, (mid i).card = j - 1 := by
    intro i
    simp only [mid]
    rw [Finset.card_erase_of_mem (ha_mem i), hTcard]
  refine ⟨0, T, Subsingleton.elim _ _, mid, ?_, ?_⟩
  · intro i
    refine ⟨Finset.ssubset_iff_subset_ne.mpr ⟨Finset.erase_subset _ _, ?_⟩, Subsingleton.elim _ _⟩
    intro h
    have h1 := hmid_card i
    rw [h, hTcard] at h1
    omega
  · intro i i' hii hsub
    have hne : mid i ≠ mid i' := by
      intro h
      have hmem' : a i ∈ mid i' := by
        simp only [mid, Finset.mem_erase]
        exact ⟨fun heq => hii (ha_inj heq), ha_mem i⟩
      rw [← h] at hmem'
      exact Finset.notMem_erase (a i) T hmem'
    exact hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hmid_card i', hmid_card i])))

lemma fan_ramsey_bound_general (j : ℕ) (hj : 2 ≤ j) :
    ∀ k, 1 ≤ k → ∀ (α : Type) [Fintype α] [DecidableEq α],
      k * (j - 1) + 1 ≤ Fintype.card α →
      ∀ χ : Finset α → Fin k, ∃ col : Fin k, ∃ top : Finset α, χ top = col ∧
        ∃ mid : Fin j → Finset α, (∀ i, mid i ⊂ top ∧ χ (mid i) = col) ∧
          ∀ i i', i ≠ i' → ¬ mid i ⊆ mid i' := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro _hk α _instF _instD hcard χ
    cases k with
    | zero => exact fan_ramsey_bound_base_one_gen j hj (by omega) χ
    | succ m =>
      have ih' := ih (by omega)
      classical
      let c : Fin (m + 2) := χ Finset.univ
      let G : Finset (Finset α) := Finset.univ.filter (fun A => A.Nonempty ∧ χ A = c)
      by_cases hant : ∃ H : Finset (Finset α),
          H ⊆ G ∧ (∀ A ∈ H, ∀ B ∈ H, A ≠ B → ¬ A ⊆ B ∧ ¬ B ⊆ A) ∧ j ≤ H.card
      · obtain ⟨H, hHG, hHanti, hjH⟩ := hant
        obtain ⟨H', hH'H, hH'card⟩ := Finset.exists_subset_card_eq hjH
        have hH'anti : ∀ A ∈ H', ∀ B ∈ H', A ≠ B → ¬ A ⊆ B ∧ ¬ B ⊆ A :=
          fun A hA B hB => hHanti A (hH'H hA) B (hH'H hB)
        have hH'χ : ∀ A ∈ H', χ A = c :=
          fun A hA => (Finset.mem_filter.mp (hHG (hH'H hA))).2.2
        let eH : ↥H' ≃ Fin j := Finset.equivFinOfCardEq hH'card
        let mid : Fin j → Finset α := fun i => (eH.symm i).1
        have hmid_mem : ∀ i, mid i ∈ H' := fun i => (eH.symm i).2
        have hmid_inj : Function.Injective mid := by
          intro i i' h
          exact eH.symm.injective (Subtype.ext h)
        have hother : ∀ i : Fin j, ∃ i' : Fin j, i' ≠ i := by
          intro i
          by_cases h : (⟨0, by omega⟩ : Fin j) = i
          · exact ⟨⟨1, by omega⟩, by rw [← h]; simp⟩
          · exact ⟨⟨0, by omega⟩, h⟩
        refine ⟨c, Finset.univ, rfl, mid, ?_, ?_⟩
        · intro i
          constructor
          · refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
            intro h
            obtain ⟨i', hi'⟩ := hother i
            have hsub : mid i' ⊆ mid i := by rw [h]; exact Finset.subset_univ _
            exact (hH'anti (mid i') (hmid_mem i') (mid i) (hmid_mem i)
              (fun heq => hi' (hmid_inj heq))).1 hsub
          · exact hH'χ (mid i) (hmid_mem i)
        · intro i i' hii hsub
          exact (hH'anti (mid i) (hmid_mem i) (mid i') (hmid_mem i')
            (fun h => hii (hmid_inj h))).1 hsub
      · have hbound : ∀ H : Finset (Finset α), H ⊆ G →
            (∀ A ∈ H, ∀ B ∈ H, A ≠ B → ¬ A ⊆ B ∧ ¬ B ⊆ A) → H.card ≤ j - 1 := by
          intro H hHG hanti
          by_contra hcon
          push Not at hcon
          exact hant ⟨H, hHG, hanti, by omega⟩
        have hGne : ∀ A ∈ G, A.Nonempty := fun A hA => (Finset.mem_filter.mp hA).2.1
        obtain ⟨S, hScard, hShit⟩ :=
          exists_hitting_set_of_no_large_antichain α G (j - 1) hGne hbound
        let T : Finset α := Finset.univ \ S
        have hTcard : (m + 1) * (j - 1) + 1 ≤ Fintype.card ↥T := by
          have hcard' : T.card = Fintype.card α - S.card := by
            rw [show T = Finset.univ \ S from rfl, Finset.card_sdiff_of_subset (Finset.subset_univ S),
              Finset.card_univ]
          rw [Fintype.card_coe, hcard']
          exact fan_ramsey_bound_arith j (m + 2) (Fintype.card α) S.card (by omega) hcard hScard
        let emb : ↥T ↪ α := Function.Embedding.subtype (· ∈ T)
        have hmapT : ∀ A : Finset ↥T, A.map emb ⊆ T := by
          intro A x hx
          rw [Finset.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact y.2
        have hne_col : ∀ A : Finset ↥T, A.Nonempty → χ (A.map emb) ≠ c := by
          intro A hA hχ
          have hBne : (A.map emb).Nonempty := Finset.Nonempty.map (f := emb) hA
          have hBG : A.map emb ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBne, hχ⟩
          obtain ⟨x, hx⟩ := hShit (A.map emb) hBG
          rw [Finset.mem_inter] at hx
          have hxT : x ∈ T := hmapT A hx.1
          rw [Finset.mem_sdiff] at hxT
          exact hxT.2 hx.2
        have hcard_sub : Fintype.card {x : Fin (m + 2) // x ≠ c} = m + 1 := by
          rw [Fintype.card_subtype]
          have hfilter : (Finset.univ.filter (fun x : Fin (m + 2) => x ≠ c)) = Finset.univ.erase c := by
            ext x; simp [Finset.mem_erase]
          rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
          omega
        let e : {x : Fin (m + 2) // x ≠ c} ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hcard_sub
        let lift : Fin (m + 1) → Fin (m + 2) := fun y => (e.symm y).1
        let χ' : Finset ↥T → Fin (m + 1) := fun A =>
          if h : A.Nonempty then e ⟨χ (A.map emb), hne_col A h⟩ else 0
        have hχ'_spec : ∀ (A : Finset ↥T) (hA : A.Nonempty), lift (χ' A) = χ (A.map emb) := by
          intro A hA
          simp only [χ', dif_pos hA, lift]
          exact congrArg Subtype.val (e.symm_apply_apply ⟨χ (A.map emb), hne_col A hA⟩)
        obtain ⟨col', top', htop'col, mid', hmid'spec, hmid'anti⟩ := ih' ↥T hTcard χ'
        have hmid'_ne : ∀ i, (mid' i).Nonempty := by
          intro i
          by_contra hcon
          rw [Finset.not_nonempty_iff_eq_empty] at hcon
          obtain ⟨i', hi'⟩ : ∃ i' : Fin j, i' ≠ i := by
            by_cases h : (⟨0, by omega⟩ : Fin j) = i
            · exact ⟨⟨1, by omega⟩, by rw [← h]; simp⟩
            · exact ⟨⟨0, by omega⟩, h⟩
          exact hmid'anti i i' (Ne.symm hi') (by rw [hcon]; exact Finset.empty_subset _)
        have htop'_ne : top'.Nonempty :=
          Finset.Nonempty.mono
            (Finset.ssubset_iff_subset_ne.mp ((hmid'spec (⟨0, by omega⟩ : Fin j)).1)).1
            (hmid'_ne _)
        refine ⟨lift col', top'.map emb, ?_, fun i => (mid' i).map emb, ?_, ?_⟩
        · rw [← hχ'_spec top' htop'_ne, htop'col]
        · intro i
          constructor
          · refine Finset.ssubset_iff_subset_ne.mpr
              ⟨Finset.map_subset_map.mpr
                (Finset.ssubset_iff_subset_ne.mp ((hmid'spec i).1)).1, ?_⟩
            intro h
            exact (Finset.ssubset_iff_subset_ne.mp ((hmid'spec i).1)).2 (Finset.map_inj.mp h)
          · rw [← hχ'_spec (mid' i) (hmid'_ne i), (hmid'spec i).2]
        · intro i i' hii hsub
          exact hmid'anti i i' hii (Finset.map_subset_map.mp hsub)

/-- Lemma 4 of the paper: the k-colour Ramsey number of the poset F_j (a maximum element over an antichain of size j) is at most k(j-1)+1. -/
theorem fan_ramsey_bound (j k d : ℕ) (hj : 2 ≤ j) (hk : 1 ≤ k) (hd : k * (j - 1) + 1 ≤ d)
    (χ : Finset (Fin d) → Fin k) : ∃ col : Fin k, has_monochromatic_fan_copy j d col χ := by
  have h := fan_ramsey_bound_general j hj k hk (Fin d) (by simpa using hd) χ
  simpa [has_monochromatic_fan_copy] using h
