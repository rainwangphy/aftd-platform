import AFTD.Prelude

/-!
# greedy_distinct_diff_next

Topic: combinatorics   Node: c1b9d44685bc

Provenance: formalization of a published result. Source: arXiv:2610.15860 (A note on the Slater–Vélez permutation), first paragraph (the greedy rule), and the 1977 paper it cites, 'Permutations of the positive integers with restrictions on the sequence of differences'.

Given the terms so far (most recent first), the next greedy term: the least positive integer not used yet whose absolute difference with the last term differs from every consecutive difference so far.
-/

/-- The next term of the greedy sequence with distinct consecutive differences. -/
noncomputable def greedy_distinct_diff_next (l : List ℕ) : ℕ :=
  sInf {c : ℕ | 0 < c ∧ c ∉ l ∧
    Int.natAbs ((c : ℤ) - l.headD 0) ∉ (l.zip l.tail).map (fun p => Int.natAbs ((p.1 : ℤ) - p.2))}
