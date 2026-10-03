import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WpropxGadgetBc

/-!
# wpropx_gadget_dom

Topic: fair_division   Node: 2fec0c415f67

Pareto domination between allocations for natural-number costs.
-/

/-- Pareto domination in `ℕ`. -/
abbrev wpropx_gadget_dom {m n : ℕ} (C : Fin n → Fin m → ℕ) (τ σ : Fin m → Fin n) : Prop :=
  (∀ i, wpropx_gadget_bc C τ i ≤ wpropx_gadget_bc C σ i) ∧
    ∃ i, wpropx_gadget_bc C τ i < wpropx_gadget_bc C σ i
