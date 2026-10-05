import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetMinSet
import AFTD.Kb.Tcs.PmFam
import AFTD.Kb.Tcs.PMSat
import AFTD.Kb.Tcs.PmFamWidth2
import AFTD.Kb.Tcs.PMState
import AFTD.Kb.Tcs.PMStateInv
import AFTD.Kb.Tcs.PMStatePot
import AFTD.Kb.Tcs.PmRerank
import AFTD.Kb.Tcs.PmRecolor
import AFTD.Kb.Tcs.PMPosetWidth2

/-!
# pm_leaf

Topic: algorithms   Node: dd895b7ec666

At a leaf with positive potential, two realisations consistent with all answers have different sets of minimal elements (so no output can be correct for both).
-/

open Finset in
/-- At a leaf with positive potential, two realisations consistent with all answers have different sets of minimal elements (so no output can be correct for both). -/
theorem pm_leaf {n : ℕ} (S : PMState n) (hI : S.Inv) (hpos : 0 < S.pot) :
    ∃ P₁ P₂ : PMPoset n, P₁.Width2 ∧ P₂.Width2 ∧ PMSat P₁ S.facts ∧ PMSat P₂ S.facts ∧
      P₁.minSet ≠ P₂.minSet := by
  have hI' := hI
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  -- a "bad pair" of alive elements that can be put in the same chain
  have hbad : ∃ a ∈ S.alive, ∃ b ∈ S.alive, a ≠ b ∧ (S.comp a = S.comp b → S.col a = S.col b) := by
    by_contra hno
    push Not at hno
    have hA : S.alive.card ≤ 2 := by
      by_contra hc
      obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.1 (by omega : 2 < S.alive.card)
      have e1 := (hno x hx y hy hxy).2
      have e2 := (hno x hx z hz hxz).2
      have e3 := (hno y hy z hz hyz).2
      cases hcx : S.col x <;> cases hcy : S.col y <;> cases hcz : S.col z <;> simp_all
    have hC : (Finset.univ.image S.comp).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro u hu v hv
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨a, ha, hax⟩ := h7 x
      obtain ⟨b, hb, hby⟩ := h7 y
      rw [← hax, ← hby]
      by_cases hab : a = b
      · rw [hab]
      · exact (hno a ha b hb hab).1
    simp only [PMState.pot] at hpos
    have : ((Finset.univ.image S.comp).card : ℤ) ≤ 1 := by exact_mod_cast hC
    have : (S.alive.card : ℤ) ≤ 2 := by exact_mod_cast hA
    linarith
  obtain ⟨a, ha, b, hb, hab, hcab⟩ := hbad
  set c' : Fin n → Bool := fun x => if S.comp x = S.comp b then
      (if S.col a = S.col b then S.col x else !S.col x) else S.col x with hc'
  have hceq : ∀ f ∈ S.facts, (c' f.1 = c' f.2.1 ↔ S.col f.1 = S.col f.2.1) := by
    intro f hf
    have hxy := h1 f hf
    simp only [hc', hxy]
    split_ifs <;> simp
  have hca : c' a = S.col a := by
    simp only [hc']
    by_cases h : S.comp a = S.comp b
    · rw [if_pos h, if_pos (hcab h)]
    · rw [if_neg h]
  have hcb : c' b = S.col a := by
    simp only [hc']
    cases hx : S.col a <;> cases hy : S.col b <;> simp
  have hsame : c' a = c' b := by rw [hca, hcb]
  have hnn : ∀ x, (0 : ℤ) ≤ S.rk x := by
    intro x
    by_cases hx : x ∈ S.alive
    · rw [h4 x hx]; exact Int.natCast_nonneg _
    · have := h5 x hx
      have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg _
      have : (0 : ℤ) ≤ (S.alive.card : ℤ) := Int.natCast_nonneg _
      linarith
  have hneg : (-1 : ℤ) < (n : ℤ) + S.alive.card := by
    have : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg _
    have : (0 : ℤ) ≤ (S.alive.card : ℤ) := Int.natCast_nonneg _
    linarith
  have hinj : ∀ z, Function.Injective (Function.update S.rk z (-1)) := by
    intro z x y hxy
    by_cases hx : x = z
    · by_cases hy : y = z
      · rw [hx, hy]
      · subst hx
        simp only [Function.update_self, Function.update_of_ne hy] at hxy
        have := hnn y; linarith
    · by_cases hy : y = z
      · subst hy
        simp only [Function.update_self, Function.update_of_ne hx] at hxy
        have := hnn x; linarith
      · simp only [Function.update_of_ne hx, Function.update_of_ne hy] at hxy
        exact h6 hxy
  have hsat : ∀ z ∈ S.alive, PMSat (pmFam c' (Function.update S.rk z (-1))) S.facts := by
    intro z hz f hf
    rw [pm_rerank S hI' c' hceq z hz (-1) hneg f hf,
      pm_recolor S.facts S.col c' S.rk (fun g hg => hceq g hg) f hf]
    exact h2 f hf
  refine ⟨pmFam c' (Function.update S.rk a (-1)), pmFam c' (Function.update S.rk b (-1)),
    pm_fam_width2 _ _ (hinj a), pm_fam_width2 _ _ (hinj b), hsat a ha, hsat b hb, ?_⟩
  intro heq
  have hb1 : b ∉ (pmFam c' (Function.update S.rk a (-1))).minSet := by
    simp only [PMPoset.minSet, Finset.mem_filter, Finset.mem_univ, true_and, not_forall]
    refine ⟨a, ?_⟩
    simp only [pmFam, Function.update_self, Function.update_of_ne (fun e => hab e.symm)]
    have := hnn b
    simp only [hsame, true_and, Bool.not_eq_false, decide_eq_true_eq]
    linarith
  have hb2 : b ∈ (pmFam c' (Function.update S.rk b (-1))).minSet := by
    simp only [PMPoset.minSet, Finset.mem_filter, Finset.mem_univ, true_and]
    intro y
    simp only [pmFam, Function.update_self, decide_eq_false_iff_not, not_and, not_lt]
    intro _
    by_cases hy : y = b
    · rw [hy, Function.update_self]
    · rw [Function.update_of_ne hy]; have := hnn y; linarith
  rw [heq] at hb1
  exact hb1 hb2
