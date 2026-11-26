import AFTD.Prelude
import AFTD.Kb.Tcs.Ks2InstanceCode
import AFTD.Kb.Tcs.Ks2InstanceOuter
import AFTD.Kb.Tcs.Ks2YesInstance

/-!
# ks2_distinct_outer_language

Topic: np_completeness   Node: 019359fe745b

Provenance: formalization of a published result. Source: arXiv:2611.27740, Problem 1.1 with a strengthening of the restriction of Section 4: no two input vectors have the same outer product (the problem only sees the outer products, and v and a unit multiple of v have the same one).

With explicit argument c : ℝ, the language over Bool (Language Bool, a set of words List Bool) of all words w for which there exist α : ℚ, d : ℕ and vs : List (ℚ × List (ℚ × ℚ)) with ks2_instance_code α d vs = w, such that the list of matrices ks2_instance_outer d p for p in vs (List.map) has no duplicates (List.Nodup: the rank-one terms v v† of the input vectors are pairwise distinct, i.e. no two input vectors agree up to a unit scalar), and ks2_yes_instance c α d vs holds.
-/

/-- Yes-instances of `KS₂(c)` whose rank-one terms `v v†` are pairwise distinct, as a language of binary words. -/
def ks2_distinct_outer_language (c : ℝ) : Language Bool :=
  {w | ∃ (α : ℚ) (d : ℕ) (vs : List (ℚ × List (ℚ × ℚ))), ks2_instance_code α d vs = w ∧
    (vs.map (ks2_instance_outer d)).Nodup ∧ ks2_yes_instance c α d vs}
