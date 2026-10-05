import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PmFam
import AFTD.Kb.Tcs.PmAnsFam

/-!
# pm_recolor

Topic: algorithms   Node: 8c36a27d12a4

Recolouring that preserves colour-equality on every fact preserves all answers.
-/

/-- Recolouring that preserves colour-equality on every fact preserves all answers. -/
theorem pm_recolor {n : ℕ} (F : List (Fin n × Fin n × PMAns)) (c c' : Fin n → Bool)
    (ρ : Fin n → ℤ) (hc : ∀ f ∈ F, (c' f.1 = c' f.2.1 ↔ c f.1 = c f.2.1)) :
    ∀ f ∈ F, (pmFam c' ρ).ans f.1 f.2.1 = (pmFam c ρ).ans f.1 f.2.1 := by
  intro f hf
  have h := hc f hf
  rw [pm_ans_fam, pm_ans_fam]
  have h' : (c' f.2.1 = c' f.1 ↔ c f.2.1 = c f.1) := by
    constructor <;> intro e <;> exact (by
      first
      | exact (h.1 e.symm).symm
      | exact (h.2 e.symm).symm)
  simp only [h, h']
