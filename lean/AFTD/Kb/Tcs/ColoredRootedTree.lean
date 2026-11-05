import AFTD.Prelude

/-!
# ColoredRootedTree

Topic: data_structures   Node: 26cbce93158a

Provenance: formalization of a published result. Source: arXiv:2611.03620 Section 2.1

A finite rooted tree properly colored with 4 colors, represented by an ancestorship partial order with a root element below all vertices, linearly ordered ancestor sets, and adjacent nodes having different colors.
-/

/-- A finite rooted tree properly 4-colored, structured as an ancestorship poset. -/
structure ColoredRootedTree where
  V : Type
  [fintype : Fintype V]
  [decEq : DecidableEq V]
  [partialOrder : PartialOrder V]
  root : V
  bot_le : ∀ v : V, root ≤ v
  down_chain : ∀ u₁ u₂ v : V, u₁ ≤ v → u₂ ≤ v → u₁ ≤ u₂ ∨ u₂ ≤ u₁
  color : V → Fin 4
  proper_coloring : ∀ u v : V, u < v → (∀ w : V, u ≤ w → w < v → w = u) → color u ≠ color v
