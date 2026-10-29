import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting

/-!
# wild_color_connecting_crosses_closed_cut

Topic: graphs   Node: 3f6322fdc3c0

Provenance: helper lemma. Structural necessity and certificate-soundness helpers for the OP-306 campaign; arXiv:2610.22142, Sections 3.3.1 and 3.3.2. These make the optimal block-partition route an equivalence at every odd order; no new exact wild-number case or bound is asserted.

For a color-connecting edge set W, every nonempty proper vertex set closed under a used color has a W edge crossing to its complement.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem wild_color_connecting_crosses_closed_cut {n k : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (W : Finset (Sym2 (Fin n)))
    (hW : simple_graph_is_color_connecting (⊤ : SimpleGraph (Fin n)) c ↑W)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (U : Finset (Fin n))
    (hU : U.Nonempty) (hproper : U ≠ Finset.univ) (hclosed : w279_closed c (c e) U) :
    ∃ (u v : Fin n) (huv : u ≠ v), u ∈ U ∧ v ∉ U ∧ s(u,v) ∈ W := by
  classical
  by_contra! hn
  let H := SimpleGraph.fromEdgeSet ({f | ∃ hf : f ∈ (⊤ : SimpleGraph (Fin n)).edgeSet, c ⟨f,hf⟩ = c e} ∪ (↑W : Set (Sym2 (Fin n))))
  have hH : H.Connected := hW.2 e
  have hstay : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ U := by
    intro u hu v hv
    rw [SimpleGraph.fromEdgeSet_adj] at hv
    rcases hv with ⟨⟨he,hc⟩ | hw,hne⟩
    · exact hclosed u hu v hne hc
    · by_contra hnv
      exact hn u v hne hu hnv (Finset.mem_coe.1 hw)
  obtain ⟨u,hu⟩ := hU
  have hall : ∀ v : Fin n, v ∈ U := by
    intro v
    obtain ⟨p⟩ := hH.preconnected u v
    have walkstay : ∀ {x y : Fin n}, H.Walk x y → x ∈ U → y ∈ U := by
      intro x y p
      induction p with
      | nil => exact id
      | cons hx p ih => exact fun hxU => ih (hstay _ hxU _ hx)
    exact walkstay p hu
  exact hproper (Finset.eq_univ_of_forall hall)
