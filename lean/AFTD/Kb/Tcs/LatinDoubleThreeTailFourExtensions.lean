import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinTableaux
import AFTD.Kb.Tcs.LatinTopRowAvailability
import AFTD.Kb.Tcs.LatinDoubleThreeTailProfileAll
import AFTD.Kb.Tcs.LatinDoubleThreeTailPermanentOfProfile

/-!
# latin_double_three_tail_four_extensions

Topic: combinatorics   Node: 6c2d8c1f2f15

Provenance: original. Related work: Proposed here as a pointwise four-extension refinement of the open counting question in https://arxiv.org/html/2610.29291v1, Conjecture 6.3. The baseline availability-permanent identity is Lemma 5.4; top-row monotonicity is Proposition 5.5. Exact evidence and the column-profile mechanism: experiments 4100, 4103 and 4106.

Conjecture: every Latin tableau of shape (k,k-1,...,4,3,3), k at least 5, extends in exactly four ways after adding the next top row of length k+1.
-/

theorem latin_double_three_tail_four_extensions (k : ℕ) (hk : 5 ≤ k) : ∀ T ∈ latin_tableaux (latin_double_three_tail_shape k), Matrix.permanent (latin_top_row_availability (latin_double_three_tail_shape k) T (k+1)) = 4 := by
  intro T hT
  exact latin_double_three_tail_permanent_of_profile k hk T (latin_double_three_tail_profile_all k hk T hT)
