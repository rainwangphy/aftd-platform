import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PmMinPre

/-!
# pm_exists_min_below

Topic: algorithms   Node: 420f9fbd6e58

Every element of a prefix lies above (or is) a minimal element of that prefix.
-/

open Finset in
/-- Every element of a prefix lies above (or is) a minimal element of that prefix. -/
theorem pm_exists_min_below {n : ℕ} (P : PMPoset n) (k : ℕ) (b : Fin n) (hb : b.val < k) :
    ∃ t ∈ pmMinPre P k, t = b ∨ P.lt t b = true := by
  set D : Finset (Fin n) := Finset.univ.filter (fun c => c.val < k ∧ (c = b ∨ P.lt c b = true))
    with hD
  have hbD : b ∈ D := by simp [hD, hb]
  obtain ⟨c, hcD, hcmin⟩ := Finset.exists_min_image D
    (fun c => (Finset.univ.filter (fun d => P.lt d c = true)).card) ⟨b, hbD⟩
  simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hcD
  refine ⟨c, ?_, hcD.2⟩
  simp only [pmMinPre, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hcD.1, fun d hd => ?_⟩
  by_contra hdc
  have hdc' : P.lt d c = true := by simpa using hdc
  have hdD : d ∈ D := by
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hd, Or.inr ?_⟩
    rcases hcD.2 with e | e
    · rw [← e]; exact hdc'
    · exact P.trans d c b hdc' e
  have hle := hcmin d hdD
  have hsub : Finset.univ.filter (fun e => P.lt e d = true) ⊂ Finset.univ.filter (fun e => P.lt e c = true) := by
    refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨d, ?_, ?_⟩
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact P.trans e d c he hdc'
    · simp [hdc']
    · simp [P.irrefl]
  have := Finset.card_lt_card hsub
  omega
