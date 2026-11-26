import AFTD.Prelude
import AFTD.Kb.Tcs.Ks2InstanceCode
import AFTD.Kb.Tcs.Ks2InstanceVector
import AFTD.Kb.Tcs.Ks2YesInstance

/-!
# ks2_distinct_language

Topic: np_completeness   Node: 456c79f10d60

Provenance: formalization of a published result. Source: arXiv:2611.27740, Problem 1.1 with the restriction of Section 4 (no multiple copies of the same vector): the set of codes of valid inputs with pairwise distinct vectors that have a signing of operator norm at most c sqrt(alpha).

With explicit argument c : ℝ, the language over Bool (Language Bool, a set of words List Bool) of all words w for which there exist α : ℚ, d : ℕ and vs : List (ℚ × List (ℚ × ℚ)) with ks2_instance_code α d vs = w, such that the list of vectors ks2_instance_vector d p for p in vs (List.map) has no duplicates (List.Nodup: the input vectors are pairwise distinct as elements of ℂ^d), and ks2_yes_instance c α d vs holds.
-/

/-- Yes-instances of `KS₂(c)` whose input vectors are pairwise distinct, as a language of binary words. -/
def ks2_distinct_language (c : ℝ) : Language Bool :=
  {w | ∃ (α : ℚ) (d : ℕ) (vs : List (ℚ × List (ℚ × ℚ))), ks2_instance_code α d vs = w ∧
    (vs.map (ks2_instance_vector d)).Nodup ∧ ks2_yes_instance c α d vs}
