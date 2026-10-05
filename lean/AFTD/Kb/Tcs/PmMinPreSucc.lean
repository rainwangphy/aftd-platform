import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PmMinPre
import AFTD.Kb.Tcs.PmExistsMinBelow

/-!
# pm_minPre_succ

Topic: algorithms   Node: 08611f490c6f

An element is minimal in the prefix of length k+1 iff it was minimal in the prefix of length k and is not above element k, or it is element k and no earlier prefix-minimal element lies below it.
-/

open Finset in
theorem pm_minPre_succ {n : ℕ} (P : PMPoset n) (k : ℕ) (hk : k < n) (a : Fin n) :
    a ∈ pmMinPre P (k + 1) ↔
      (a ∈ pmMinPre P k ∧ P.lt ⟨k, hk⟩ a = false) ∨
      (a = ⟨k, hk⟩ ∧ ∀ t ∈ pmMinPre P k, P.lt t ⟨k, hk⟩ = false) := by
  simp only [pmMinPre, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ha, hmin⟩
    by_cases hak : a.val < k
    · left
      exact ⟨⟨hak, fun b hb => hmin b (by omega)⟩, hmin _ (by simp)⟩
    · right
      have hax : a = ⟨k, hk⟩ := Fin.ext (by simp; omega)
      refine ⟨hax, fun t ht => ?_⟩
      rw [← hax]; exact hmin t (by omega)
  · rintro (⟨⟨hak, hmin⟩, hx⟩ | ⟨hax, hmin⟩)
    · refine ⟨by omega, fun b hb => ?_⟩
      by_cases hbk : b.val < k
      · exact hmin b hbk
      · have : b = ⟨k, hk⟩ := Fin.ext (by simp; omega)
        rw [this]; exact hx
    · subst hax
      refine ⟨by simp, fun b hb => ?_⟩
      by_cases hbk : b.val < k
      · by_contra hbx
        have hbx' : P.lt b ⟨k, hk⟩ = true := by simpa using hbx
        obtain ⟨t, ht, htb⟩ := pm_exists_min_below P k b hbk
        have : P.lt t ⟨k, hk⟩ = true := by
          rcases htb with e | e
          · rw [e]; exact hbx'
          · exact P.trans _ _ _ e hbx'
        rw [hmin t (by simpa [pmMinPre] using ht)] at this
        exact absurd this (by simp)
      · have : b = ⟨k, hk⟩ := Fin.ext (by simp; omega)
        rw [this]; exact P.irrefl _
