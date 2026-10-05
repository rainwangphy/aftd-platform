import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PmFam
import AFTD.Kb.Tcs.PmAnsFam
import AFTD.Kb.Tcs.PMState
import AFTD.Kb.Tcs.PMStateInv
import AFTD.Kb.Tcs.PMStatePot
import AFTD.Kb.Tcs.PmRecolor

/-!
# pm_inv_merge

Topic: algorithms   Node: 632dd3cbc961

Adversary case: two different components are merged (answer ∥); the second component is recoloured if necessary. The number of components drops by at most one.
-/

open Finset in
/-- Adversary case: two different components are merged (answer `∥`); the second component is recoloured if necessary. The number of components drops by at most one. -/
theorem pm_inv_merge {n : ℕ} (S : PMState n) (hI : S.Inv) (a b : Fin n)
    (hcomp : S.comp a ≠ S.comp b) :
    ({ S with
        col := fun x => if S.comp x = S.comp b then
            (if S.col a = S.col b then !S.col x else S.col x) else S.col x
        comp := fun x => if S.comp x = S.comp b then S.comp a else S.comp x
        facts := (a, b, PMAns.inc) :: S.facts } : PMState n).Inv ∧
    S.pot ≤ ({ S with
        col := fun x => if S.comp x = S.comp b then
            (if S.col a = S.col b then !S.col x else S.col x) else S.col x
        comp := fun x => if S.comp x = S.comp b then S.comp a else S.comp x
        facts := (a, b, PMAns.inc) :: S.facts } : PMState n).pot + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  set c' : Fin n → Bool := fun x => if S.comp x = S.comp b then
            (if S.col a = S.col b then !S.col x else S.col x) else S.col x with hc'
  set k' : Fin n → Fin n := fun x => if S.comp x = S.comp b then S.comp a else S.comp x
    with hk'
  -- colour equality is preserved inside a component
  have hceq : ∀ x y : Fin n, S.comp x = S.comp y → (c' x = c' y ↔ S.col x = S.col y) := by
    intro x y hxy
    simp only [hc', hxy]
    split_ifs <;> simp
  have hca : c' a = S.col a := by simp [hc', hcomp]
  have hcb : c' b ≠ S.col a := by
    simp only [hc']
    cases h : S.col a <;> cases h' : S.col b <;> simp [h, h']
  refine ⟨⟨?_, ?_, ?_, h4, h5, h6, ?_⟩, ?_⟩
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · simp [hk', hcomp]
    · have := h1 f hf
      simp only [hk', this]
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · show (pmFam c' S.rk).ans a b = PMAns.inc
      have hne : ¬ c' a = c' b := by rw [hca]; exact fun e => hcb e.symm
      have hne' : ¬ c' b = c' a := fun e => hne e.symm
      simp [pm_ans_fam, hne, hne']
    · show (pmFam c' S.rk).ans f.1 f.2.1 = f.2.2
      rw [pm_recolor S.facts S.col c' S.rk (fun g hg => hceq _ _ (h1 g hg)) f hf]
      exact h2 f hf
  · intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · intro _ _ _
      show c' a ≠ c' b
      rw [hca]; exact fun e => hcb e.symm
    · intro hx hy hxy
      show c' f.1 ≠ c' f.2.1
      rw [Ne, hceq _ _ (h1 f hf)]
      exact h3 f hf hx hy hxy
  · intro x
    obtain ⟨a', ha', hax⟩ := h7 x
    exact ⟨a', ha', by simp only [hk', hax]⟩
  · simp only [PMState.pot]
    have hsub : Finset.univ.image S.comp ⊆ insert (S.comp b) (Finset.univ.image k') := by
      intro t ht
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 ht
      by_cases hx : S.comp x = S.comp b
      · rw [hx]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_image.2 ⟨x, Finset.mem_univ _, by simp [hk', hx]⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have : ((Finset.univ.image S.comp).card : ℤ) ≤ (Finset.univ.image k').card + 1 := by exact_mod_cast this
    linarith
