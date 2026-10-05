import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseInDomain
import AFTD.Kb.GameTheoryEconomics.FseSurjective
import AFTD.Kb.GameTheoryEconomics.FseSPAll
import AFTD.Kb.GameTheoryEconomics.FsePath
import AFTD.Kb.GameTheoryEconomics.FseExistsAvoid

/-!
# fse_mem_range

Topic: mechanism_design   Node: 792d39991f85

A surjective mechanism that is strategyproof for all scaling functions always outputs some agent's reported location.
-/

/-- A surjective mechanism that is strategyproof for all scaling functions always outputs some agent's reported location. -/
lemma fse_mem_range {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hSP : fse_SPAll f) (hsurj : fse_Surjective f)
    (x : Fin n → ℝ) (hx : fse_InDomain x) : ∃ i, f x = x i := by
  by_contra hcon
  push Not at hcon
  set c := f x with hcdef
  obtain ⟨d, hd, hdc⟩ := fse_exists_avoid {c} (Set.finite_singleton c)
  obtain ⟨e, he, hecd⟩ := fse_exists_avoid {c, d} (Set.toFinite _)
  simp only [Set.mem_singleton_iff] at hdc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hecd
  obtain ⟨w, hw, hfw⟩ := hsurj d hd
  let w' : Fin n → ℝ := fun i => if w i = c then e else w i
  have hw' : fse_InDomain w' := by
    intro i; simp only [w']; split_ifs
    · exact he
    · exact hw i
  have h1 : f w' = d := by
    apply fse_path f hSP w w' hw hw' d hfw
    intro j hj
    simp only [w'] at hj
    split_ifs at hj with hjc
    · rw [hjc]; exact fun h => hdc h.symm
    · exact absurd rfl hj
  have h2 : f w' = c := by
    apply fse_path f hSP x w' hx hw' c rfl
    intro j _ h
    exact hcon j h.symm
  exact hdc (h1.symm.trans h2)
