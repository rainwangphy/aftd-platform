import AFTD.Prelude

/-!
# SimpleGraphOrientation

Topic: statistical_mechanics   Node: 7e623a49dfee

Provenance: formalization of a published result. Source: Diestel, Graph Theory (5th ed. 2017), Section 1.5

An orientation of a finite simple graph G assigns to each edge an ordered pair of its endpoints.
-/

/-- An orientation of a simple graph assigns to each edge an ordered pair of its endpoints. -/
structure SimpleGraphOrientation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  dir : G.edgeFinset → V × V
  dir_fst_snd : ∀ e : G.edgeFinset, s((dir e).1, (dir e).2) = e.val
