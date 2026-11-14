import AFTD.Prelude
import AFTD.Kb.Tcs.ModularQueensAttack

/-!
# is_non_attacking_queens

Topic: combinatorics   Node: 894bde0c0a07

Provenance: formalization of a published result. Source: arXiv:2611.14754 Sec. 1

A finite set of queens in (Z/nZ)^d is mutually non-attacking if no two distinct queens in the set attack each other.
-/

/-- A set of queens in (Z/nZ)^d is non-attacking if no two distinct queens attack each other. -/
def is_non_attacking_queens {d n : ℕ} (s : Finset (Fin d → ZMod n)) : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ¬ modular_queens_attack x y
