import AFTD.Prelude
import AFTD.Kb.Tcs.NonadaptiveMstStoppingTime
import AFTD.Kb.Optimization.IsMstCertificate
import AFTD.Kb.Optimization.TreeSubmodularGoalValueZero

/-!
# nonadaptive_mst_stopping_time_of_isTree

Topic: approximation   Node: 7e41e4bb8da4

Provenance: formalization of a published result. Source: arXiv:2610.40844 Sec. 2

If G is a tree, then under any binary edge realization α and any querying order π, the stopping time is 0 because the unique spanning tree is certified before querying any edges.
-/

/-- On a tree, any edge order stops in 0 queries since the tree itself is already certified as the unique spanning tree. -/
theorem nonadaptive_mst_stopping_time_of_isTree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hT : G.IsTree) (π : List G.edgeSet) (α : G.edgeSet → Bool) :
    nonadaptive_mst_stopping_time G π α = 0 := by
  dsimp [nonadaptive_mst_stopping_time]
  apply Nat.sInf_eq_zero.mpr
  left
  exact tree_submodular_goal_value_zero_is_mst_certificate G hT _
