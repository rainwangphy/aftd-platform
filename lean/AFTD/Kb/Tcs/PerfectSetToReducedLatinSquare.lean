import AFTD.Prelude

/-!
# perfect_set_to_reduced_latin_square

Topic: combinatorics   Node: 87a2d7c952b1

Provenance: formalization of a published result. Source: arXiv:2611.07118, Perfect Partitions of Regular Bipartite Graphs, Lemma 1.3

For a positive natural number n, a finite set S of permutations of Fin n, and two elements r, j : Fin n, `perfect_set_to_reduced_latin_square S r j` equals j if r = 0; if r ≠ 0 and there exists a permutation σ ∈ S such that σ 0 = r, it equals σ j for a chosen such σ; and if no such permutation exists in S, it equals j.
-/

/-- Reconstruct a reduced Latin square from a perfect set of permutations. -/
noncomputable def perfect_set_to_reduced_latin_square {n : ℕ} [NeZero n]
    (S : Finset (Equiv.Perm (Fin n))) (r j : Fin n) : Fin n := if r = 0 then j
  else if h : ∃ σ ∈ S, σ 0 = r then (Classical.choose h) j
  else j
