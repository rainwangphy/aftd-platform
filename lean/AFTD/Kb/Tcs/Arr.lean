import AFTD.Prelude

/-!
# Arr

Topic: combinatorics   Node: 7f81cf905e78

Provenance: formalization of a published result. Source: arXiv:2611.05397, Section 2.2, Definition 1: Ranking and Unranking Permutations in Heap's Order

The set of arrangement arrays of order $m$ is represented as the type of functions from $\mathrm{Fin}\,m$ to $\mathrm{Fin}\,m$.
-/

/-- The type of arrangement arrays of order m, represented as functions from Fin m to Fin m. -/
abbrev Arr (m : ℕ) : Type := Fin m → Fin m
