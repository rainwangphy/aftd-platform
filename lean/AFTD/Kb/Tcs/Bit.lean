import AFTD.Prelude

/-!
# bit

Topic: circuits   Node: 9fbd2c312128

Provenance: formalization of a published result. Source: arXiv:2610.19174, Listing A.1

The real embedding of a Boolean value, sending false to 0 and true to 1.
-/

/-- Convert a boolean value to a real number (0 or 1). -/
def bit (b : Bool) : ℝ := if b then 1 else 0
