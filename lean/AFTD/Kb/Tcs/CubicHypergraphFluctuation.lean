import AFTD.Prelude
import AFTD.Kb.Tcs.CubicHypergraph
import AFTD.Kb.Tcs.HypergraphState
import AFTD.Kb.Tcs.MagicFluctuation

/-!
# cubicHypergraphFluctuation

Topic: quantum   Node: 9d6e469e9164

Provenance: formalization of a published result. Source: Quantum 8, 1422 (2024)

For an n-qubit 3-uniform hypergraph H : CubicHypergraph n, cubicHypergraphFluctuation n H is the magic fluctuation magicFluctuation n (hypergraphState n (H.image Subtype.val)).
-/

/-- The magic fluctuation of a 3-uniform hypergraph state. -/
noncomputable def cubicHypergraphFluctuation (n : ℕ) (H : CubicHypergraph n) : ℝ := magicFluctuation n (hypergraphState n (H.image Subtype.val))
