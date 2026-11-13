import AFTD.Prelude

/-!
# forest_carpool_tail_envelope

Topic: online_algorithms   Node: 9070a7654fd0

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

The proposed one-sided discrepancy tail envelope is 3/8 at level 2 and otherwise two to the negative Fibonacci number of the level.
-/

noncomputable def forest_carpool_tail_envelope (k : ℕ) : ℝ := if k = 2 then 3 / 8 else (1 / 2 : ℝ) ^ Nat.fib k
