import AFTD.Prelude

/-!
# cycle_labeling_complete

Topic: combinatorics   Node: 3402cd38c0ac

Provenance: formalization of a published result. Source: arXiv:2610.08889 (Consecutive Cycle Sums), Sec. 1–2 (complete n-cycle; arcs and arc sums), for an arbitrary placement of 1, …, n around the cycle as in list entry OP-121 (the paper places them in increasing order). Arcs are all windows of length 1..n of the doubled list.

Placing the labels L (a permutation of 1, …, n) in order around an n-cycle gives a complete cycle: every k ∈ {1, …, n(n+1)/2} is the sum of the labels on some arc (l ∈ {1, …, n} consecutive positions starting at some position i < n).
-/

/-- The labels `L` (a list of length `n`), placed in order around an `n`-cycle, form a complete cycle: `L` is a permutation of `1, …, n`, and every `k ∈ {1, …, n(n+1)/2}` is the sum of the labels on some arc, i.e. on `l ∈ {1, …, n}` consecutive positions of the cycle starting at a position `i < n`. -/
def cycle_labeling_complete (n : ℕ) (L : List ℕ) : Prop :=
  L.Perm (List.range' 1 n) ∧ ∀ k ∈ Finset.Icc 1 (n * (n + 1) / 2),
    ∃ i < n, ∃ l ∈ Finset.Icc 1 n, (((L ++ L).drop i).take l).sum = k
