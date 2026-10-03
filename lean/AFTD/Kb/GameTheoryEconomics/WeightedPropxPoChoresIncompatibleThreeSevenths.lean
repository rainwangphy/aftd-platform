import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NoWeightedPropxPoOfNatCheck
import AFTD.Kb.GameTheoryEconomics.IsWeightedPropxChores
import AFTD.Kb.GameTheoryEconomics.IsParetoOptimalChores
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetWpropxNat
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetDom

/-!
# weighted_propx_po_chores_incompatible_three_sevenths

Topic: fair_division   Node: 3342d703589e

For two agents with shares (3/7, 4/7), six chores and strictly positive additive costs (262,111,258,100,1,103) and (135,75,113,1,43,53), no allocation is weighted PROPX and Pareto optimal.
-/

/-- Costs: agent 0 pays (262, 111, 258, 100, 1, 103), agent 1 pays (135, 75, 113, 1, 43, 53). -/
def wpropx_gadget_cost_c : Fin 2 → Fin 6 → ℕ :=
  ![![262, 111, 258, 100, 1, 103], ![135, 75, 113, 1, 43, 53]]

/-- Each of the five weighted PROPX allocations is dominated by one of four allocations. -/
def wpropx_gadget_ok_c (σ : Fin 6 → Fin 2) : Prop :=
  wpropx_gadget_wpropx_nat wpropx_gadget_cost_c ![3, 4] 7 σ →
    wpropx_gadget_dom wpropx_gadget_cost_c ![0, 1, 1, 1, 0, 0] σ ∨
      wpropx_gadget_dom wpropx_gadget_cost_c ![0, 0, 1, 0, 0, 1] σ ∨
      wpropx_gadget_dom wpropx_gadget_cost_c ![1, 1, 0, 1, 0, 0] σ ∨
      wpropx_gadget_dom wpropx_gadget_cost_c ![0, 1, 1, 1, 0, 1] σ

instance wpropx_gadget_ok_c_decidable : DecidablePred wpropx_gadget_ok_c := fun σ => by
  unfold wpropx_gadget_ok_c; infer_instance

/-- Kernel check over all 64 allocations. -/
lemma wpropx_gadget_check_c :
    ∀ a b c d e f : Fin 2, wpropx_gadget_ok_c ![a, b, c, d, e, f] := by
  decide

theorem weighted_propx_po_chores_incompatible_three_sevenths :
    ∃ c : Fin 2 → Fin 6 → ℝ, (∀ i e, 0 < c i e) ∧
      ¬ ∃ σ : Fin 6 → Fin 2, is_weighted_propx_chores c ![3 / 7, 4 / 7] σ ∧
        is_pareto_optimal_chores c σ := by
  refine ⟨fun i e => (wpropx_gadget_cost_c i e : ℝ), fun i e => ?_, ?_⟩
  · have : 0 < wpropx_gadget_cost_c i e := by revert i e; decide
    show (0 : ℝ) < (wpropx_gadget_cost_c i e : ℝ)
    exact_mod_cast this
  have hw : (![3 / 7, 4 / 7] : Fin 2 → ℝ) =
      fun i => (((![3, 4] : Fin 2 → ℕ) i : ℕ) : ℝ) / ((7 : ℕ) : ℝ) := by
    funext i; fin_cases i <;> norm_num
  rw [hw]
  refine no_weighted_propx_po_of_nat_check _ _ _ (by norm_num) fun σ h => ?_
  have hσ : σ = ![σ 0, σ 1, σ 2, σ 3, σ 4, σ 5] := by funext x; fin_cases x <;> rfl
  have hc := wpropx_gadget_check_c (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5)
  rw [← hσ] at hc
  rcases hc h with h' | h' | h' | h'
  all_goals exact ⟨_, h'⟩
