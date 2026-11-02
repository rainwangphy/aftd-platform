import AFTD.Prelude
import AFTD.Kb.Tcs.TreeRoutingCost
import AFTD.Kb.Tcs.IsSubcubicTree

/-!
# tbt_opt

Topic: approximation   Node: 11ccfece3674

Provenance: formalization of a published result. Source: arXiv:2610.39863, Section 3

For a finite type V and a simple graph T on V, tbt_opt T is the infimum in ℕ of the routing costs tree_routing_cost T H id over all subcubic trees H on V.
-/

/-- The optimal Tree in Binary Tree (TBT) routing cost without Steiner nodes. -/
noncomputable def tbt_opt {V : Type} [Fintype V] (T : SimpleGraph V) : ℕ := open Classical in
  sInf { c : ℕ | ∃ (H : SimpleGraph V), is_subcubic_tree H ∧ tree_routing_cost T H id = c }
