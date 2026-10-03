import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# wpropx_gadget_bc

Topic: fair_division   Node: 669202ee1964

Agent i's cost for her own bundle under an allocation, for natural-number costs.
-/

/-- Agent `i`'s cost for her own bundle under `σ`, in `ℕ`. -/
abbrev wpropx_gadget_bc {m n : ℕ} (C : Fin n → Fin m → ℕ) (σ : Fin m → Fin n) (i : Fin n) : ℕ :=
  ∑ e ∈ bundle_of σ i, C i e
