import AFTD.Prelude

/-!
# pell_number

Topic: automata   Node: 786f28590b4e

Provenance: formalization of a published result. Source: arXiv:2610.08525 Sec. 5

The Pell numbers are defined by P(0) = 0, P(1) = 1, and P(m+2) = P(m) + 2 P(m+1).
-/

/-- The Pell numbers P_m defined by P_0 = 0, P_1 = 1, and P_{m+2} = P_m + 2 P_{m+1}. -/
def pell_number : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | m + 2 => pell_number m + 2 * pell_number (m + 1)
