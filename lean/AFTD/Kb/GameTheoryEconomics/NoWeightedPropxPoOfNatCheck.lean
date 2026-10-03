import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsParetoOptimalChores
import AFTD.Kb.GameTheoryEconomics.IsWeightedPropxChores
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetDom
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetOfDom
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetToNat
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetWpropxNat

/-!
# no_weighted_propx_po_of_nat_check

Topic: fair_division   Node: e4013d19bc61

Reduction for kernel checking: if, for natural-number costs C and shares num/den, every allocation that is weighted PROPX (multiplied through by den) is Pareto-dominated in N, then no allocation is weighted PROPX and Pareto optimal for the real costs.
-/

theorem no_weighted_propx_po_of_nat_check {m n : ℕ} (C : Fin n → Fin m → ℕ) (num : Fin n → ℕ) (den : ℕ)
    (hden : 0 < den)
    (hok : ∀ σ, wpropx_gadget_wpropx_nat C num den σ → ∃ τ, wpropx_gadget_dom C τ σ) :
    ¬ ∃ σ, is_weighted_propx_chores (fun i e => (C i e : ℝ)) (fun i => (num i : ℝ) / den) σ ∧
      is_pareto_optimal_chores (fun i e => (C i e : ℝ)) σ := by
  rintro ⟨σ, hw, hpo⟩
  obtain ⟨τ, hτ⟩ := hok σ (wpropx_gadget_to_nat C num den hden σ hw)
  exact hpo ⟨τ, wpropx_gadget_of_dom C τ σ hτ⟩
