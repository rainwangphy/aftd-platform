import AFTD.Prelude

/-!
# persuasion_lym_sum_le

Topic: mechanism_design   Node: 2805390e78e8

LYM, relative form. If PP is an antichain of subsets of U and f(|T|) · C(|U|, |T|) ≤ B for every T ∈ PP, then ∑_{T ∈ PP} f(|T|) ≤ B.
-/

open Finset in
/-- **LYM, relative form.** If `PP` is an antichain of subsets of `U` and
`f(|T|) · C(|U|, |T|) ≤ B` for every `T ∈ PP`, then `∑_{T ∈ PP} f(|T|) ≤ B`. -/
lemma persuasion_lym_sum_le {α : Type*} [DecidableEq α] (U : Finset α) (PP : Finset (Finset α))
    (hP : ∀ T ∈ PP, T ⊆ U) (hA : IsAntichain (· ⊆ ·) (PP : Set (Finset α))) (f : ℕ → ℕ) (B : ℕ)
    (hf : ∀ T ∈ PP, f T.card * U.card.choose T.card ≤ B) :
    ∑ T ∈ PP, f T.card ≤ B := by
  classical
  let g : Finset α → Finset {x // x ∈ U} := fun T => T.subtype (· ∈ U)
  have hcard : ∀ T ∈ PP, (g T).card = T.card := by
    intro T hT
    simp only [g, card_subtype]
    rw [filter_true_of_mem (fun x hx => hP T hT hx)]
  have hsub : ∀ T ∈ PP, ∀ T' ∈ PP, g T ⊆ g T' → T ⊆ T' := by
    intro T hT T' hT' h x hx
    have hxU := hP T hT hx
    have : (⟨x, hxU⟩ : {x // x ∈ U}) ∈ g T := by simp [g, hx]
    have := h this
    simpa [g] using this
  have hinj : Set.InjOn g (PP : Set (Finset α)) := by
    intro T hT T' hT' h
    exact Finset.Subset.antisymm (hsub T hT T' hT' h.le) (hsub T' hT' T hT h.ge)
  have hanti : IsAntichain (· ⊆ ·) ((PP.image g : Finset _) : Set (Finset {x // x ∈ U})) := by
    intro s hs s' hs' hne hss
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs hs'
    obtain ⟨T, hT, rfl⟩ := hs
    obtain ⟨T', hT', rfl⟩ := hs'
    have hTT : T ≠ T' := fun h => hne (h ▸ rfl)
    exact hA hT hT' hTT (hsub T hT T' hT' hss)
  have hlym := lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜 := ℝ) hanti
  rw [sum_image hinj, Fintype.card_coe] at hlym
  have hpos : ∀ T ∈ PP, (0 : ℝ) < (U.card.choose T.card : ℝ) := by
    intro T hT
    exact_mod_cast Nat.choose_pos (Finset.card_le_card (hP T hT))
  have key : ∀ T ∈ PP, (f T.card : ℝ) ≤ (B : ℝ) * ((U.card.choose (g T).card : ℝ))⁻¹ := by
    intro T hT
    rw [hcard T hT, ← div_eq_mul_inv, le_div_iff₀ (hpos T hT)]
    exact_mod_cast hf T hT
  have : (∑ T ∈ PP, (f T.card : ℝ)) ≤ B := by
    calc (∑ T ∈ PP, (f T.card : ℝ)) ≤ ∑ T ∈ PP, (B : ℝ) * ((U.card.choose (g T).card : ℝ))⁻¹ :=
          sum_le_sum key
      _ = (B : ℝ) * ∑ T ∈ PP, ((U.card.choose (g T).card : ℝ))⁻¹ := by rw [mul_sum]
      _ ≤ (B : ℝ) * 1 := mul_le_mul_of_nonneg_left hlym (Nat.cast_nonneg _)
      _ = B := mul_one _
  exact_mod_cast this
