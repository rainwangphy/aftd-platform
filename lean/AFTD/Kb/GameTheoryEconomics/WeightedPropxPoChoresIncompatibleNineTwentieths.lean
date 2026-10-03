import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NoWeightedPropxPoOfNatCheck
import AFTD.Kb.GameTheoryEconomics.IsWeightedPropxChores
import AFTD.Kb.GameTheoryEconomics.IsParetoOptimalChores
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetWpropxNat
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetDom

/-!
# weighted_propx_po_chores_incompatible_nine_twentieths

Topic: fair_division   Node: 97fd84c5233d

For two agents with shares (9/20, 11/20), six chores and strictly positive additive costs (114,222,1,177,64,166) and (56,209,71,164,1,154), no allocation is weighted PROPX and Pareto optimal.
-/

/-- Costs: agent 0 pays (114, 222, 1, 177, 64, 166), agent 1 pays (56, 209, 71, 164, 1, 154). -/
def wpropx_gadget_cost_b : Fin 2 → Fin 6 → ℕ :=
  ![![114, 222, 1, 177, 64, 166], ![56, 209, 71, 164, 1, 154]]

/-- Each of the four weighted PROPX allocations is dominated by one of four allocations. -/
def wpropx_gadget_ok_b (σ : Fin 6 → Fin 2) : Prop :=
  wpropx_gadget_wpropx_nat wpropx_gadget_cost_b ![9, 11] 20 σ →
    wpropx_gadget_dom wpropx_gadget_cost_b ![0, 1, 0, 1, 1, 0] σ ∨
      wpropx_gadget_dom wpropx_gadget_cost_b ![1, 0, 0, 1, 1, 0] σ ∨
      wpropx_gadget_dom wpropx_gadget_cost_b ![1, 1, 0, 0, 1, 0] σ ∨
      wpropx_gadget_dom wpropx_gadget_cost_b ![0, 0, 0, 1, 1, 1] σ

instance wpropx_gadget_ok_b_decidable : DecidablePred wpropx_gadget_ok_b := fun σ => by
  unfold wpropx_gadget_ok_b; infer_instance

/-- Kernel check over all 64 allocations. -/
lemma wpropx_gadget_check_b :
    ∀ a b c d e f : Fin 2, wpropx_gadget_ok_b ![a, b, c, d, e, f] := by
  decide

theorem weighted_propx_po_chores_incompatible_nine_twentieths :
    ∃ c : Fin 2 → Fin 6 → ℝ, (∀ i e, 0 < c i e) ∧
      ¬ ∃ σ : Fin 6 → Fin 2, is_weighted_propx_chores c ![9 / 20, 11 / 20] σ ∧
        is_pareto_optimal_chores c σ := by
  refine ⟨fun i e => (wpropx_gadget_cost_b i e : ℝ), fun i e => ?_, ?_⟩
  · have : 0 < wpropx_gadget_cost_b i e := by revert i e; decide
    show (0 : ℝ) < (wpropx_gadget_cost_b i e : ℝ)
    exact_mod_cast this
  have hw : (![9 / 20, 11 / 20] : Fin 2 → ℝ) =
      fun i => (((![9, 11] : Fin 2 → ℕ) i : ℕ) : ℝ) / ((20 : ℕ) : ℝ) := by
    funext i; fin_cases i <;> norm_num
  rw [hw]
  refine no_weighted_propx_po_of_nat_check _ _ _ (by norm_num) fun σ h => ?_
  have hσ : σ = ![σ 0, σ 1, σ 2, σ 3, σ 4, σ 5] := by funext x; fin_cases x <;> rfl
  have hc := wpropx_gadget_check_b (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5)
  rw [← hσ] at hc
  rcases hc h with h' | h' | h' | h'
  all_goals exact ⟨_, h'⟩
