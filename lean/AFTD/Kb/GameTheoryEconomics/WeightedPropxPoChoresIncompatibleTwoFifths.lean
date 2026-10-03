import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NoWeightedPropxPoOfNatCheck
import AFTD.Kb.GameTheoryEconomics.IsWeightedPropxChores
import AFTD.Kb.GameTheoryEconomics.IsParetoOptimalChores
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetWpropxNat
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetDom

/-!
# weighted_propx_po_chores_incompatible_two_fifths

Topic: fair_division   Node: d5309588c46b

For two agents with shares (2/5, 3/5), five chores and strictly positive additive costs (38,1,111,72,48) and (31,54,113,40,1), no allocation is weighted PROPX and Pareto optimal.
-/

/-- Costs: agent 0 pays (38, 1, 111, 72, 48), agent 1 pays (31, 54, 113, 40, 1). -/
def wpropx_gadget_cost_a : Fin 2 → Fin 5 → ℕ :=
  ![![38, 1, 111, 72, 48], ![31, 54, 113, 40, 1]]

/-- The only weighted PROPX allocations, (0,0,1,1,0) with costs (87, 153) and (1,1,0,1,1) with
costs (111, 126), are dominated by (1,0,1,0,1) with costs (73, 145) and (0,0,1,0,1) with costs
(111, 114). -/
def wpropx_gadget_ok_a (σ : Fin 5 → Fin 2) : Prop :=
  wpropx_gadget_wpropx_nat wpropx_gadget_cost_a ![2, 3] 5 σ →
    wpropx_gadget_dom wpropx_gadget_cost_a ![1, 0, 1, 0, 1] σ ∨
      wpropx_gadget_dom wpropx_gadget_cost_a ![0, 0, 1, 0, 1] σ

instance wpropx_gadget_ok_a_decidable : DecidablePred wpropx_gadget_ok_a := fun σ => by
  unfold wpropx_gadget_ok_a; infer_instance

/-- Kernel check over all 32 allocations. -/
lemma wpropx_gadget_check_a : ∀ a b c d e : Fin 2, wpropx_gadget_ok_a ![a, b, c, d, e] := by
  decide

theorem weighted_propx_po_chores_incompatible_two_fifths :
    ∃ c : Fin 2 → Fin 5 → ℝ, (∀ i e, 0 < c i e) ∧
      ¬ ∃ σ : Fin 5 → Fin 2, is_weighted_propx_chores c ![2 / 5, 3 / 5] σ ∧
        is_pareto_optimal_chores c σ := by
  refine ⟨fun i e => (wpropx_gadget_cost_a i e : ℝ), fun i e => ?_, ?_⟩
  · have : 0 < wpropx_gadget_cost_a i e := by revert i e; decide
    show (0 : ℝ) < (wpropx_gadget_cost_a i e : ℝ)
    exact_mod_cast this
  have hw : (![2 / 5, 3 / 5] : Fin 2 → ℝ) =
      fun i => (((![2, 3] : Fin 2 → ℕ) i : ℕ) : ℝ) / ((5 : ℕ) : ℝ) := by
    funext i; fin_cases i <;> norm_num
  rw [hw]
  refine no_weighted_propx_po_of_nat_check _ _ _ (by norm_num) fun σ h => ?_
  have hσ : σ = ![σ 0, σ 1, σ 2, σ 3, σ 4] := by funext x; fin_cases x <;> rfl
  have hc := wpropx_gadget_check_a (σ 0) (σ 1) (σ 2) (σ 3) (σ 4)
  rw [← hσ] at hc
  rcases hc h with h' | h'
  · exact ⟨_, h'⟩
  · exact ⟨_, h'⟩
