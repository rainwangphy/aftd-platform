import AFTD.Prelude

/-!
# reduced_latin_square_to_perfect_set

Topic: combinatorics   Node: c4b6314fe716

Provenance: formalization of a published result. Source: arXiv:2611.07118, Perfect Partitions of Regular Bipartite Graphs, Lemma 1.3

For a function R : Fin n → Fin n → Fin n with n ≠ 0, `reduced_latin_square_to_perfect_set R` is the finite set of permutations of Fin n obtained as the image of {r : Fin n | r ≠ 0} under the mapping that sends each r to the permutation given by R r if R r is bijective, and to the identity permutation 1 otherwise.
-/

/-- Extract the set of non-zero row permutations of an n × n matrix. -/
noncomputable def reduced_latin_square_to_perfect_set {n : ℕ} [NeZero n]
    (R : Fin n → Fin n → Fin n) : Finset (Equiv.Perm (Fin n)) := (Finset.univ.erase 0).image fun r =>
    if h : Function.Bijective (R r) then Equiv.ofBijective (R r) h else 1
