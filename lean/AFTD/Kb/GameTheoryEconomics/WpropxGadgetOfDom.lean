import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ParetoDominatesChores
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetAv
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetDom

/-!
# wpropx_gadget_of_dom

Topic: fair_division   Node: 38ca0cd102df

Pareto domination for natural-number costs implies Pareto domination for the costs cast to the reals.
-/

lemma wpropx_gadget_of_dom {m n : ℕ} (C : Fin n → Fin m → ℕ) (τ σ : Fin m → Fin n)
    (h : wpropx_gadget_dom C τ σ) :
    pareto_dominates_chores (fun i e => (C i e : ℝ)) τ σ := by
  obtain ⟨hle, j, hlt⟩ := h
  refine ⟨fun i => ?_, j, ?_⟩
  · simp only [wpropx_gadget_av]; exact_mod_cast hle i
  · simp only [wpropx_gadget_av]; exact_mod_cast hlt
