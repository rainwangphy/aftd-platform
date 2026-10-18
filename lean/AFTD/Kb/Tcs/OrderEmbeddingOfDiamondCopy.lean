import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy
import AFTD.Kb.Tcs.DiamondPoset
import AFTD.Kb.Tcs.InstPartialOrderDiamondPoset

/-!
# orderEmbedding_of_diamond_copy

Topic: combinatorics   Node: aaa119feb509

Provenance: helper lemma. step towards diamond_poset_ramsey_number_le

If the colouring χ of the subsets of Fin d has a monochromatic combinatorial j-diamond copy in colour col, then there is an order embedding of DiamondPoset j into Finset (Fin d) all of whose values have colour col. Hence the combinatorial predicate agrees with the order-embedding based definition of a monochromatic induced copy.
-/

/-- A monochromatic combinatorial diamond copy (bot, j incomparable middles, top) is a monochromatic induced copy in the order-embedding sense: it yields an order embedding of DiamondPoset j into the Boolean lattice whose image is constant under the colouring. -/
theorem orderEmbedding_of_diamond_copy (j d : ℕ) {k : ℕ} (col : Fin k) (χ : Finset (Fin d) → Fin k)
    (h : has_monochromatic_diamond_copy j d col χ) :
    ∃ e : DiamondPoset j ↪o Finset (Fin d), ∀ x : DiamondPoset j, χ (e x) = col := by
  obtain ⟨B, T, hBT, hB, hT, M, hMid, hInc⟩ := h
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
      | top => exact ⟨fun _ => trivial, fun _ => (hMid i).2.1.le⟩
    | top =>
      cases b with
      | bot => exact ⟨hBT.not_ge, fun h => h.elim⟩
      | mid i => exact ⟨(hMid i).2.1.not_ge, fun h => h.elim⟩
      | top => exact ⟨fun _ => trivial, fun _ => le_refl T⟩
  refine ⟨OrderEmbedding.ofMapLEIff g key, fun x => ?_⟩
  cases x with
  | bot => exact hB
  | mid i => exact (hMid i).2.2
  | top => exact hT
