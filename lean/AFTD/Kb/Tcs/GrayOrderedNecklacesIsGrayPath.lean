import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BitwordNecklaceAdjacent
import AFTD.Kb.Tcs.BrgcWord

/-!
# gray_ordered_necklaces_is_gray_path

Topic: combinatorics   Node: b66d51e53e44

Provenance: original. Related work: arXiv:2610.24758: Optimal single-track Gray codes from Gray-ordered necklaces

The list D_n of non-constant binary necklaces of length n, ordered by the rank of their first occurrences in the binary reflected Gray code, forms a Gray path in the necklace graph Q_n: consecutive necklaces in this order are adjacent in Q_n.
-/

/-- The list of non-constant binary necklaces ordered by first occurrence in the binary reflected Gray code forms a Gray path in the necklace graph. -/
def gray_ordered_necklaces_is_gray_path (n : ℕ) : Prop :=
  ∀ t t' : ℕ, brgc_necklace_first_rank n t → brgc_necklace_first_rank n t' → t < t' →
    (∀ s, t < s → s < t' → ¬ brgc_necklace_first_rank n s) →
    bitword_necklace_adjacent n (brgc_word t) (brgc_word t')
