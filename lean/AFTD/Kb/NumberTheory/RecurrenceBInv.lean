import AFTD.Prelude

/-!
# recurrence_b_inv

Topic: elementary_number_theory   Node: 842b7e084200

Provenance: formalization of a published result. Source: arXiv:2610.34300 Proposition 7

The inverse transition map for recurrence (B) on (ℤ/3ℤ)^k for k ≥ 2, sending (u_0, ..., u_{k-1}) to (u_{k-1} - u_{k-2}^2, u_0, ..., u_{k-2}).
-/

/-- Explicit inverse transition map for recurrence B on (ZMod 3)^k when k ≥ 2. -/
def recurrence_b_inv (k : ℕ) (hk : 2 ≤ k) (u : Fin k → ZMod 3) : Fin k → ZMod 3 := fun i =>
  if i.val = 0 then
    u ⟨k - 1, by omega⟩ - (u ⟨k - 2, by omega⟩)^2
  else
    u ⟨i.val - 1, by omega⟩
