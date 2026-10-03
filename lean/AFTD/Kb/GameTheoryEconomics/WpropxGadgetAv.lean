import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetBc

/-!
# wpropx_gadget_av

Topic: fair_division   Node: dd198c0f8b3a

For natural-number costs cast to the reals, the additive cost of a bundle is the cast of the natural-number cost.
-/

lemma wpropx_gadget_av {m n : ℕ} (C : Fin n → Fin m → ℕ) (σ : Fin m → Fin n) (i : Fin n) :
    additive_valuation (fun e => (C i e : ℝ)) (bundle_of σ i) = (wpropx_gadget_bc C σ i : ℝ) := by
  unfold additive_valuation wpropx_gadget_bc; push_cast; rfl
