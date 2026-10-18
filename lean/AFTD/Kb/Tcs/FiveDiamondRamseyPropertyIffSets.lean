import AFTD.Prelude
import AFTD.Kb.Tcs.DiamondPoset
import AFTD.Kb.Tcs.PosetRamseyProperty
import AFTD.Kb.Tcs.InstPartialOrderDiamondPoset

/-!
# five_diamond_ramsey_property_iff_sets

Topic: combinatorics   Node: 96f671109acb

Provenance: helper lemma. step towards op_270_five_diamond_poset_ramsey_number

A k-colouring of the subsets of Fin d contains a monochromatic induced copy of the j-diamond exactly when it has, in one colour, a set B, a set T with B ⊂ T, and j pairwise incomparable sets M i with B ⊂ M i ⊂ T for all i.
-/

/-- Unfolds poset_ramsey_property for DiamondPoset j into an explicit bottom/top/antichain condition on the sets. -/
theorem five_diamond_ramsey_property_iff_sets (j k d : ℕ) :
    poset_ramsey_property (DiamondPoset j) k d ↔
      ∀ c : Finset (Fin d) → Fin k,
        ∃ (col : Fin k) (B T : Finset (Fin d)) (M : Fin j → Finset (Fin d)),
          c B = col ∧ c T = col ∧ (∀ i, c (M i) = col) ∧
            B ⊂ T ∧ (∀ i, B ⊂ M i ∧ M i ⊂ T) ∧
              ∀ i i', i ≠ i' → ¬ (M i ⊆ M i') := by
  constructor
  · rintro h c
    obtain ⟨f, col, hf⟩ := h c
    refine ⟨col, f DiamondPoset.bot, f DiamondPoset.top, fun i => f (DiamondPoset.mid i),
      hf _, hf _, fun i => hf _, ?_, ?_, ?_⟩
    · exact f.lt_iff_lt.mpr (by rw [lt_iff_le_not_ge]; exact ⟨trivial, id⟩)
    · intro i
      exact ⟨f.lt_iff_lt.mpr (by rw [lt_iff_le_not_ge]; exact ⟨trivial, id⟩),
        f.lt_iff_lt.mpr (by rw [lt_iff_le_not_ge]; exact ⟨trivial, id⟩)⟩
    · intro i i' hne hle
      exact hne (f.le_iff_le.mp hle)
  · intro h c
    obtain ⟨col, B, T, M, hB, hT, hM, hBT, hMid, hInc⟩ := h c
    let g : DiamondPoset j → Finset (Fin d) := fun x =>
      match x with
      | .bot => B
      | .mid i => M i
      | .top => T
    have key : ∀ a b : DiamondPoset j, g a ≤ g b ↔ a ≤ b := by
      intro a b
      cases a with
      | bot =>
        cases b with
        | bot => exact ⟨fun _ => trivial, fun _ => le_refl B⟩
        | mid i => exact ⟨fun _ => trivial, fun _ => (hMid i).1.le⟩
        | top => exact ⟨fun _ => trivial, fun _ => hBT.le⟩
      | mid i =>
        cases b with
        | bot => exact ⟨(hMid i).1.not_ge, fun h => h.elim⟩
        | mid i' =>
          refine ⟨fun hle => ?_, fun heq => ?_⟩
          · by_contra hne
            exact hInc i i' hne hle
          · subst heq
            exact le_refl _
        | top => exact ⟨fun _ => trivial, fun _ => (hMid i).2.le⟩
      | top =>
        cases b with
        | bot => exact ⟨hBT.not_ge, fun h => h.elim⟩
        | mid i => exact ⟨(hMid i).2.not_ge, fun h => h.elim⟩
        | top => exact ⟨fun _ => trivial, fun _ => le_refl T⟩
    refine ⟨OrderEmbedding.ofMapLEIff g key, col, fun x => ?_⟩
    cases x with
    | bot => exact hB
    | mid i => exact hM i
    | top => exact hT
