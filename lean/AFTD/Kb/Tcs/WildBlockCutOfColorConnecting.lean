import AFTD.Prelude
import AFTD.Kb.Tcs.WildColorConnectingCrossesClosedCut
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_block_cut_of_color_connecting

Topic: graphs   Node: bf4b5a0e8642

Provenance: helper lemma. Structural necessity and certificate-soundness helpers for the OP-306 campaign; arXiv:2610.22142, Sections 3.3.1 and 3.3.2. These make the optimal block-partition route an equivalence at every odd order; no new exact wild-number case or bound is asserted.

A rooted vertex partition whose blocks contain both endpoints of every wild edge has an edge of every used color across every nonempty proper block cut whenever the wild edge set is color-connecting.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem wild_block_cut_of_color_connecting {n k q : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (W : Finset (Sym2 (Fin n)))
    (hW : simple_graph_is_color_connecting (⊤ : SimpleGraph (Fin n)) c ↑W)
    (p : Fin n → Fin q) (r : Fin q → Fin n) (hr : ∀ t, p (r t) = t)
    (hstay : ∀ (u v : Fin n) (huv : u ≠ v), s(u,v) ∈ W → p u = p v) :
    ∀ (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (S : Finset (Fin q)),
      S.Nonempty → S ≠ Finset.univ →
      ∃ (u v : Fin n) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧ c ⟨s(u,v),wild_kn_mem huv⟩ = c e := by
  classical
  intro e S hS hproper
  by_contra! hno
  let U : Finset (Fin n) := Finset.univ.filter fun v => p v ∈ S
  have hU : U.Nonempty := by
    obtain ⟨t,ht⟩ := hS
    refine ⟨r t,Finset.mem_filter.2 ⟨Finset.mem_univ _,?_⟩⟩
    rwa [hr]
  have hUproper : U ≠ Finset.univ := by
    intro hh
    apply hproper
    apply Finset.eq_univ_of_forall
    intro t
    have ht : r t ∈ U := hh ▸ Finset.mem_univ _
    simpa only [U,Finset.mem_filter,Finset.mem_univ,true_and,hr] using ht
  have hclosed : w279_closed c (c e) U := by
    intro u hu v huv hc
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _,?_⟩
    by_contra hv
    exact hno u v huv (Finset.mem_filter.1 hu).2 hv hc
  obtain ⟨u,v,huv,hu,hv,hw⟩ := wild_color_connecting_crosses_closed_cut c W hW e U hU hUproper hclosed
  have huS := (Finset.mem_filter.1 hu).2
  apply hv
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _,(hstay u v huv hw) ▸ huS⟩
