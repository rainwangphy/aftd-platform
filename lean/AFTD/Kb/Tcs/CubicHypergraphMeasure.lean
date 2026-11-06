import AFTD.Prelude
import AFTD.Kb.Tcs.CubicHypergraph
import AFTD.Kb.Tcs.CubicEdge

/-!
# cubicHypergraphMeasure

Topic: quantum   Node: 1197c0818035

Provenance: formalization of a published result. Source: Quantum 8, 1422 (2024)

For each natural number n, cubicHypergraphMeasure n is the probability measure on CubicHypergraph n induced by the uniform probability mass function PMF.uniformOfFintype.
-/

/-- The uniform probability measure on 3-uniform hypergraphs on Fin n. -/
noncomputable def cubicHypergraphMeasure (n : ℕ) : MeasureTheory.Measure (CubicHypergraph n) := (PMF.uniformOfFintype (CubicHypergraph n)).toMeasure
