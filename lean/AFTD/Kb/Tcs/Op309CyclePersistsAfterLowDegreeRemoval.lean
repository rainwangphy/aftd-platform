import AFTD.Prelude

/-!
# op309_cycle_persists_after_low_degree_removal

Topic: graphs   Node: 4a5d082cbf9f

Provenance: helper lemma. Cycle persistence under one-to-two P3 switches for OP-309.

A graph cycle survives if a vertex with at most one neighbor is removed and every other edge is retained.
-/

theorem op309_cycle_persists_after_low_degree_removal
    {V : Type*} [Fintype V] [DecidableEq V] (H H' : SimpleGraph V) (b : V)
    (hleaf : ∀ x y, H.Adj b x → H.Adj b y → x = y)
    (hkeep : ∀ x y, x ≠ b → y ≠ b → H.Adj x y → H'.Adj x y)
    (hc : ¬ H.IsAcyclic) : ¬ H'.IsAcyclic := by
  classical
  intro ha
  apply hc
  intro u p hp
  have hb : b ∉ p.support := by
    intro hm
    have htwo := hp.ncard_neighborSet_toSubgraph_eq_two hm
    have hsmall : (p.toSubgraph.neighborSet b).Subsingleton := by
      intro x hx y hy
      exact hleaf x y (p.toSubgraph.adj_sub hx) (p.toSubgraph.adj_sub hy)
    have hone : (p.toSubgraph.neighborSet b).ncard ≤ 1 :=
      Set.ncard_le_one_iff_subsingleton.mpr hsmall
    omega
  have htransfer : ∀ e ∈ p.edges, e ∈ H'.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : p.toSubgraph.Adj x y := p.adj_toSubgraph_iff_mem_edges.mpr he
      have hxb : x ≠ b := by
        intro heq
        subst x
        exact hb (p.mem_support_of_adj_toSubgraph hxy)
      have hyb : y ≠ b := by
        intro heq
        subst y
        exact hb (p.mem_support_of_adj_toSubgraph hxy.symm)
      exact hkeep x y hxb hyb (p.toSubgraph.adj_sub hxy)
  exact ha (p.transfer H' htransfer) (hp.transfer htransfer)
