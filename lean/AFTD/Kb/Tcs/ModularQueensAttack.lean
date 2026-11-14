import AFTD.Prelude

/-!
# modular_queens_attack

Topic: combinatorics   Node: 3a2b058ab001

Provenance: formalization of a published result. Source: arXiv:2611.14754 Sec. 1

Two queens at positions x and y in (Z/nZ)^d attack each other if their difference x - y is a nonzero scalar multiple of a nonzero vector with coordinates in {-1, 0, 1}.
-/

/-- Two queens at positions x and y in (Z/nZ)^d attack each other if x - y = c * v for nonzero c and nonzero v in {-1,0,1}^d. -/
def modular_queens_attack {d n : ℕ} (x y : Fin d → ZMod n) : Prop := ∃ (c : ZMod n) (v : Fin d → SignType), c ≠ 0 ∧ v ≠ 0 ∧
    ∀ i : Fin d, x i - y i = c * (SignType.cast (v i) : ZMod n)
