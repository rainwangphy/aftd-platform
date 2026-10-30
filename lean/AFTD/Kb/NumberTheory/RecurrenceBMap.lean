import AFTD.Prelude

/-!
# recurrence_b_map

Topic: elementary_number_theory   Node: f2ccac03fb83

Provenance: formalization of a published result. Source: arXiv:2610.34300 Proposition 7

The state transition map T : (ℤ/3ℤ)^k → (ℤ/3ℤ)^k for recurrence (B), sending (w_0, ..., w_{k-1}) to (w_1, ..., w_{k-1}, w_0 + w_{k-1}^2).
-/

/-- State transition map for recurrence B on (ZMod 3)^k. -/
def recurrence_b_map (k : ℕ) (w : Fin k → ZMod 3) : Fin k → ZMod 3 := fun i =>
  if h : (i : ℕ) + 1 < k then
    w ⟨i.val + 1, h⟩
  else
    w ⟨0, by omega⟩ + (w ⟨k - 1, by omega⟩)^2
