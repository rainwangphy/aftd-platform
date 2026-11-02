import AFTD.Prelude
import AFTD.Kb.Tcs.TreeRoutingCost
import AFTD.Kb.Tcs.IsSubcubicTree

/-!
# tbt_sn_opt

Topic: approximation   Node: ddcebebd3de4

Provenance: formalization of a published result. Source: arXiv:2610.39863, Section 3

For a finite type V and a simple graph T on V, tbt_sn_opt T is the infimum in ℕ of the routing costs tree_routing_cost T H f over all finite types W, subcubic trees H on W, and injective maps f : V ↪ W.
-/

/-- The optimal Tree in Binary Tree with Steiner Nodes (TBT-SN) routing cost. -/
noncomputable def tbt_sn_opt {V : Type} [Fintype V] (T : SimpleGraph V) : ℕ := open Classical in
  sInf { c : ℕ | ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W) (_ : is_subcubic_tree H)
    (f : V ↪ W), tree_routing_cost T H f = c }
