import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialRGraph
import AFTD.Kb.Physics.InstDecidableRelPathGraph

/-!
# instDecidableRelPetrialRGraphAdj

Topic: combinatorics   Node: a263c970cd1a

Provenance: formalization of a published result. Source: arXiv:2611.07503 Section 3

For every natural number m, adjacency between vertices in the graph R_m is decidable.
-/

/-- Decidability of adjacency in the graph R_m. -/
instance instDecidableRelPetrialRGraphAdj (m : ℕ) : DecidableRel (petrial_R_graph m).Adj := by
  intro a b
  change Decidable (match a, b with
    | none, none => False
    | none, some (_, v) => v = 2
    | some (_, v), none => v = 2
    | some (i₁, v₁), some (i₂, v₂) => i₁ = i₂ ∧ (SimpleGraph.pathGraph 5).Adj v₁ v₂)
  match a, b with
  | none, none => exact isFalse False.elim
  | none, some (i, v) => infer_instance
  | some (i, v), none => infer_instance
  | some (i₁, v₁), some (i₂, v₂) => infer_instance
