import AFTD.Prelude

/-!
# cycle_power_sum_range_double

Topic: combinatorics   Node: b6007dd1fb27

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

A sum over the first 2n indices equals the sum over n consecutive even-odd pairs.
-/

open Finset

theorem cycle_power_sum_range_double (n : ℕ) (f : ℕ → ℕ) :
    (range (2 * n)).sum f = (range n).sum (fun i => f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [hn, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    omega
