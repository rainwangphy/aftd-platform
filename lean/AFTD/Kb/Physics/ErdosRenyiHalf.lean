import AFTD.Prelude

/-!
# erdos_renyi_half

Topic: quantum_mechanics   Node: 47ae8563d1ec

Provenance: formalization of a published result. Source: Erdős and Rényi (1959), On Random Graphs I; Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

For a natural number n, erdos_renyi_half n is the MeasureTheory.Measure on SimpleGraph (Fin n) given by SimpleGraph.binomialRandom (Fin n) with edge probability parameter 1/2.
-/

/-- The Erdős-Rényi G(n, 1/2) probability measure on simple graphs on Fin n. -/
noncomputable def erdos_renyi_half (n : ℕ) : MeasureTheory.Measure (SimpleGraph (Fin n)) := SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩
