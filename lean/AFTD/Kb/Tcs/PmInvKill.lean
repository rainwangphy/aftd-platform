import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PmFam
import AFTD.Kb.Tcs.PMState
import AFTD.Kb.Tcs.PMStateInv
import AFTD.Kb.Tcs.PMStatePot
import AFTD.Kb.Tcs.PmRerank

/-!
# pm_inv_kill

Topic: algorithms   Node: 2614dc03e320

Adversary case: comparison of two alive elements of the same component and colour; the larger one (z) dies and is re-ranked just below all previously dead elements.
-/

open Finset in
/-- Adversary case: comparison of two alive elements of the same component and colour; the larger one (`z`) dies and is re-ranked just below all previously dead elements. -/
theorem pm_inv_kill {n : ℕ} (S : PMState n) (hI : S.Inv) (z w : Fin n)
    (hz : z ∈ S.alive) (hw : w ∈ S.alive) (hzw : z ≠ w)
    (hcz : S.comp w = S.comp z)
    (f : Fin n × Fin n × PMAns)
    (hfsat : (pmFam S.col (Function.update S.rk z ((n : ℤ) + S.alive.card - 1))).ans
        f.1 f.2.1 = f.2.2)
    (hfcomp : S.comp f.1 = S.comp f.2.1) (hfz : f.1 = z ∨ f.2.1 = z) :
    ({ S with
        rk := Function.update S.rk z ((n : ℤ) + S.alive.card - 1)
        alive := S.alive.erase z
        facts := f :: S.facts } : PMState n).Inv ∧
    S.pot ≤ ({ S with
        rk := Function.update S.rk z ((n : ℤ) + S.alive.card - 1)
        alive := S.alive.erase z
        facts := f :: S.facts } : PMState n).pot + 1 := by
  have hI' := hI
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  set r : ℤ := (n : ℤ) + S.alive.card - 1 with hr
  have hcard2 : 2 ≤ S.alive.card := by
    have : ({z, w} : Finset (Fin n)) ⊆ S.alive := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hz
      · rw [Finset.mem_singleton.1 hx]; exact hw
    have h := Finset.card_le_card this
    rwa [Finset.card_pair hzw] at h
  have hcardE : ((S.alive.erase z).card : ℤ) = S.alive.card - 1 := by
    rw [Finset.card_erase_of_mem hz]
    have : 1 ≤ S.alive.card := by omega
    push_cast [Nat.cast_sub this]
    ring
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hfcomp
    · exact h1 g hg
  · intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hfsat
    · show (pmFam S.col (Function.update S.rk z r)).ans g.1 g.2.1 = g.2.2
      rw [pm_rerank S hI' S.col (fun _ _ => Iff.rfl) z hz r (by rw [hr]; linarith) g hg]
      exact h2 g hg
  · intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · intro hx hy _
      rcases hfz with e | e
      · rw [e] at hx; exact absurd hx (Finset.notMem_erase _ _)
      · rw [e] at hy; exact absurd hy (Finset.notMem_erase _ _)
    · intro hx hy hxy
      exact h3 g hg (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy
  · intro x hx
    have hxz : x ≠ z := Finset.ne_of_mem_erase hx
    show Function.update S.rk z r x = x.val
    rw [Function.update_of_ne hxz]
    exact h4 x (Finset.mem_of_mem_erase hx)
  · intro x hx
    show (n : ℤ) + (S.alive.erase z).card ≤ Function.update S.rk z r x
    rw [hcardE]
    by_cases hxz : x = z
    · subst hxz; rw [Function.update_self, hr]; linarith
    · rw [Function.update_of_ne hxz]
      have hxa : x ∉ S.alive := fun h => hx (Finset.mem_erase.2 ⟨hxz, h⟩)
      have := h5 x hxa
      linarith
  · have hfresh : ∀ y, y ≠ z → S.rk y ≠ r := by
      intro y hy e
      by_cases hya : y ∈ S.alive
      · rw [h4 y hya] at e
        have : (y.val : ℤ) < n := by exact_mod_cast y.isLt
        have : (2 : ℤ) ≤ S.alive.card := by exact_mod_cast hcard2
        rw [hr] at e; linarith
      · have := h5 y hya
        rw [hr] at e; linarith
    intro x y hxy
    show x = y
    by_cases hx : x = z
    · by_cases hy : y = z
      · rw [hx, hy]
      · subst hx
        simp only [Function.update_self, Function.update_of_ne hy] at hxy
        exact absurd hxy.symm (hfresh y hy)
    · by_cases hy : y = z
      · subst hy
        simp only [Function.update_self, Function.update_of_ne hx] at hxy
        exact absurd hxy (hfresh x hx)
      · simp only [Function.update_of_ne hx, Function.update_of_ne hy] at hxy
        exact h6 hxy
  · intro x
    obtain ⟨a', ha', hax⟩ := h7 x
    by_cases haz : a' = z
    · refine ⟨w, Finset.mem_erase.2 ⟨fun e => hzw e.symm, hw⟩, ?_⟩
      show S.comp w = S.comp x
      rw [hcz, ← haz, hax]
    · exact ⟨a', Finset.mem_erase.2 ⟨haz, ha'⟩, hax⟩
  · simp only [PMState.pot]
    rw [hcardE]
    linarith
