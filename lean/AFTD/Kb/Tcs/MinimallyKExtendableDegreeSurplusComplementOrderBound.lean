import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.MinimallyKExtendableDegreeSurplusZeroCodegreeCompleteBipartite
import AFTD.Kb.Tcs.GraphZeroCodegreeNeighborCompleteBipartiteOrderBound

/-!
# minimally_k_extendable_degree_surplus_complement_order_bound

Topic: graphs   Node: e80747341c99

Provenance: helper lemma. OP-1957: combine the general bridge theorem with the parameterized root-layer count. Not yet Lean-proved.

A minimally k-extendable graph of minimum degree at least 2k+r, with 2≤r≤d and complement maximum degree at most d, has order bounded by r²n≤r²(1+d²)+d(d−1) max(d−r²,0).
-/

theorem minimally_k_extendable_degree_surplus_complement_order_bound
    (k n d r : ℕ) (hr : 2 ≤ r) (hrd : r ≤ d)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k) (hdegree : 2*k+r ≤ G.minDegree)
    (hmax : ∀ u, (Gᶜ).degree u ≤ d) :
    r*r*n ≤ r*r*(1+d*d) + d*(d-1)*(d-r*r) := by
  have hcomplete : ∀ u v : Fin n, u ≠ v → ¬ (Gᶜ).Adj u v →
      (∀ x, ¬ ((Gᶜ).Adj u x ∧ (Gᶜ).Adj v x)) →
      ∃ A B : Finset (Fin n), A.card = r ∧ B.card = r ∧
        (∀ a ∈ A, (Gᶜ).Adj u a) ∧ (∀ b ∈ B, (Gᶜ).Adj v b) ∧
        ∀ a ∈ A, ∀ b ∈ B, (Gᶜ).Adj a b := by
    intro u v huv hnonadj hfar
    have huvG : G.Adj u v := by
      by_contra h
      exact hnonadj ((SimpleGraph.compl_adj G u v).2 ⟨huv, h⟩)
    exact minimally_k_extendable_degree_surplus_zero_codegree_complete_bipartite
      k n r hr G hmin hdegree u v huvG hfar
  exact graph_zero_codegree_neighbor_complete_bipartite_order_bound
    n d r hr hrd (Gᶜ) hmax hcomplete
