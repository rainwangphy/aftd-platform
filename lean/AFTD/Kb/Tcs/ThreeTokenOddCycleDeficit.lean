import AFTD.Prelude

/-!
# three_token_odd_cycle_deficit

Topic: graphs   Node: 51b8f5adf535

Provenance: original. Related work: arXiv:2611.22830 "Independent sets in the 2-token graph of a cycle and kings on the torus"; OP-2010

For a natural number n, three_token_odd_cycle_deficit n equals (n - 1) * (n - 2) / 6 - 1 if 3 divides n, and (n - 1) * (n - 2) / 6 otherwise.
-/

/-- Quadratic independence deficit d(n) for the 3-token graph of C_n. -/
def three_token_odd_cycle_deficit (n : ℕ) : ℕ := if 3 ∣ n then (n - 1) * (n - 2) / 6 - 1 else (n - 1) * (n - 2) / 6
