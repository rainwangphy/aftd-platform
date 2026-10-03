import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.IsWeightedPropxChores
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetBc
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetTot
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetWpropxNat

/-!
# wpropx_gadget_to_nat

Topic: fair_division   Node: 0d72c116a708

Weighted PROPX for natural-number costs cast to the reals with shares num_i/den implies its natural-number version multiplied through by den.
-/

lemma wpropx_gadget_to_nat {m n : ℕ} (C : Fin n → Fin m → ℕ) (num : Fin n → ℕ) (den : ℕ)
    (hden : 0 < den) (σ : Fin m → Fin n)
    (h : is_weighted_propx_chores (fun i e => (C i e : ℝ)) (fun i => (num i : ℝ) / den) σ) :
    wpropx_gadget_wpropx_nat C num den σ := by
  intro i e he
  have h1 := h i e he
  have hsplit : additive_valuation (fun e => (C i e : ℝ)) (bundle_of σ i \ {e}) =
      (wpropx_gadget_bc C σ i : ℝ) - C i e := by
    rw [Finset.sdiff_singleton_eq_erase]
    unfold additive_valuation wpropx_gadget_bc
    push_cast
    rw [Finset.sum_erase_eq_sub he]
  have htot : additive_valuation (fun e => (C i e : ℝ)) Finset.univ =
      (wpropx_gadget_tot C i : ℝ) := by
    unfold additive_valuation wpropx_gadget_tot; push_cast; rfl
  simp only at h1
  rw [hsplit, htot, div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hden)] at h1
  have : (den : ℝ) * wpropx_gadget_bc C σ i ≤
      den * C i e + num i * wpropx_gadget_tot C i := by linarith
  exact_mod_cast this
