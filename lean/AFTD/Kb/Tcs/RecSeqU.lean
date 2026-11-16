import AFTD.Prelude
import AFTD.Kb.Tcs.RecSeqR

/-!
# rec_seq_u

Topic: combinatorics   Node: 992d8bbeedd9

Provenance: formalization of a published result. Source: arXiv:2611.17360 line 118

The sequence `rec_seq_u : ℕ → ℤ` is defined recursively by `rec_seq_u 0 = 0`, `rec_seq_u 1 = 1`, and `rec_seq_u (k + 1) = 2 * rec_seq_u k - rec_seq_u (k - rec_seq_r k)` for all integers `k ≥ 1` (where subtraction on indices is truncated subtraction on `ℕ`).
-/

/-- The integer sequence u with u 0 = 0, u 1 = 1, and u (k + 1) = 2 * u k - u (k - rec_seq_r k). -/
noncomputable def rec_seq_u (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | 1 => 1
  | k + 1 => 2 * rec_seq_u k - rec_seq_u (k - rec_seq_r k)
termination_by n
decreasing_by
  · omega
  · have : k - rec_seq_r k ≤ k := Nat.sub_le k (rec_seq_r k)
    omega
