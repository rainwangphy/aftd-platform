import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinTableaux
import AFTD.Kb.Tcs.LatinDoubleThreeTailProfile
import AFTD.Kb.Tcs.LatinDoubleThreeTailProfileBase
import AFTD.Kb.Tcs.LatinDoubleThreeTailShapeRowLenSucc
import AFTD.Kb.Tcs.LatinDoubleThreeTailProfileSucc

/-!
# latin_double_three_tail_profile_all

Topic: combinatorics   Node: 1fa09db766cb

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

Every Latin tableau in the double-3-tail staircase family has the three canonical column-symbol profiles (nine profiles before permuting the first three columns).
-/

theorem latin_double_three_tail_profile_all (k : ℕ) (hk : 5 ≤ k) : ∀ T ∈ latin_tableaux (latin_double_three_tail_shape k), latin_double_three_tail_profile k T := by
  induction k, hk using Nat.le_induction with
  | base => exact latin_double_three_tail_profile_base
  | succ k hk ih => exact latin_double_three_tail_profile_succ k hk ih
