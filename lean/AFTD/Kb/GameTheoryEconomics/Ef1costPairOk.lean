import AFTD.Prelude

/-!
# ef1cost_pair_ok

Topic: fair_division   Node: 06fe078ea1cf

Two-bundle EF1 condition: the owner of `A`, with costs `w`, is EF1 towards `B`.
-/

/-- Two-bundle EF1 condition: the owner of `A`, with costs `w`, is EF1 towards `B`. -/
def ef1cost_pair_ok {m : ℕ} (w : Fin m → ℝ) (A B : Finset (Fin m)) : Prop :=
  ∑ j ∈ A, w j ≤ ∑ j ∈ B, w j ∨ ∃ e ∈ A, ∑ j ∈ A, w j - w e ≤ ∑ j ∈ B, w j
