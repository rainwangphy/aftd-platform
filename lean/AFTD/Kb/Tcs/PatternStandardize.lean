import AFTD.Prelude

/-!
# pattern_standardize

Topic: combinatorics   Node: a71b98e29dc5

Provenance: helper lemma. step towards extension_depth_mono_of_pattern_containment

The standardization of a list of naturals: replace each entry by its rank, i.e. the number of entries of the list that are ≤ it.
-/

/-- Replace each entry of a list of naturals by its rank (the count of entries ≤ it), its order type as a standard permutation. -/
def pattern_standardize (l : List ℕ) : List ℕ := l.map (fun x => (l.filter (fun y => y ≤ x)).length)
