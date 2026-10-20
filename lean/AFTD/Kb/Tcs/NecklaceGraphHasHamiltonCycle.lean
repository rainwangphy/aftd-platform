import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BitwordNecklaceAdjacent
import AFTD.Kb.Tcs.BrgcWord

/-!
# necklace_graph_has_hamilton_cycle

Topic: combinatorics   Node: 1466747f7183

Provenance: original. Related work: arXiv:2610.24758: Optimal single-track Gray codes from Gray-ordered necklaces

There exists an indexing cycle of the non-constant necklaces of length n such that the first m = (2^n - 2) / n values are distinct valid first-occurrence Gray code ranks of non-constant necklaces, every first-occurrence Gray code rank of a non-constant necklace of length n appears at some index i < m, and for every i < m, the necklace of cycle i is adjacent in the necklace graph to the necklace of cycle ((i + 1) % m).
-/

/-- The necklace graph Q_n has a Hamilton cycle visiting all non-constant binary necklaces of length n in order. -/
def necklace_graph_has_hamilton_cycle (n : ℕ) : Prop :=
  ∃ cycle : ℕ → ℕ,
    let m := (2 ^ n - 2) / n
    (∀ i < m, brgc_necklace_first_rank n (cycle i)) ∧
    (∀ i < m, ∀ j < m, cycle i = cycle j → i = j) ∧
    (∀ t, brgc_necklace_first_rank n t → ∃ i < m, cycle i = t) ∧
    ∀ i < m,
      bitword_necklace_adjacent n (brgc_word (cycle i))
        (brgc_word (cycle ((i + 1) % m)))
