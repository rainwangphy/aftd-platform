import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinColumnSymbols

/-!
# latin_double_three_tail_profile

Topic: combinatorics   Node: 5364d2c42622

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

The proposed column profile: among the first three columns, two contain [1,k-1] and one contains [1,k-2] together with k; intermediate columns contain initial intervals; the final two columns partition {1,2,3} into a pair and a singleton.
-/

def latin_double_three_tail_profile (k : ℕ)
    (T : (latin_double_three_tail_shape k).cells → ℕ) : Prop :=
  ∃ s ∈ Finset.Icc 1 3, ∃ c : ℕ, c < 3 ∧
    (∀ j, j < 3 → latin_column_symbols (latin_double_three_tail_shape k) T j =
      if j = c then Finset.Icc 1 (k - 2) ∪ {k} else Finset.Icc 1 (k - 1)) ∧
    (∀ j, 3 ≤ j → j < k - 2 →
      latin_column_symbols (latin_double_three_tail_shape k) T j = Finset.Icc 1 (k - j)) ∧
    latin_column_symbols (latin_double_three_tail_shape k) T (k - 2) = Finset.Icc 1 3 \ {s} ∧
    latin_column_symbols (latin_double_three_tail_shape k) T (k - 1) = {s}
