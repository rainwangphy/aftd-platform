import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetBc
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetTot

/-!
# wpropx_gadget_wpropx_nat

Topic: fair_division   Node: 5c1353518d71

Weighted PROPX for natural-number costs and shares num_i/den, multiplied through by den.
-/

/-- Weighted PROPX with shares `num i / den`, multiplied through by `den`, in `ℕ`. -/
abbrev wpropx_gadget_wpropx_nat {m n : ℕ} (C : Fin n → Fin m → ℕ) (num : Fin n → ℕ) (den : ℕ)
    (σ : Fin m → Fin n) : Prop :=
  ∀ i, ∀ e ∈ bundle_of σ i,
    den * wpropx_gadget_bc C σ i ≤ den * C i e + num i * wpropx_gadget_tot C i
