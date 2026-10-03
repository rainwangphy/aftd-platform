import AFTD.Prelude

/-!
# wpropx_gadget_tot

Topic: fair_division   Node: 8c573006213d

Agent i's cost for all chores, for natural-number costs.
-/

/-- Agent `i`'s cost for all chores, in `ℕ`. -/
abbrev wpropx_gadget_tot {m n : ℕ} (C : Fin n → Fin m → ℕ) (i : Fin n) : ℕ :=
  ∑ e, C i e
