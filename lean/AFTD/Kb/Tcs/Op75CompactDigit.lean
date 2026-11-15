import AFTD.Prelude

/-!
# op75_compact_digit

Topic: np_completeness   Node: b9993239c563

Provenance: helper lemma. OP-75, arXiv:2610.06092, one-pass subset-sum construction; a helper toward interval verification.

The digit selector x ↦ max(0, min(1, 4x−1)) used in the one-pass reduction.
-/

def op75_compact_digit (x : ℝ) : ℝ := max 0 (min 1 (4*x-1))
