import AFTD.Prelude
import AFTD.Kb.Tcs.WildColorConnectingCrossesClosedCut
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq

/-!
# wild_odd_color_connecting_closed_block_card_ge_three

Topic: graphs   Node: e6a8542288ef

Provenance: helper lemma. Structural necessity and certificate-soundness helpers for the OP-306 campaign; arXiv:2610.22142, Sections 3.3.1 and 3.3.2. These make the optimal block-partition route an equivalence at every odd order; no new exact wild-number case or bound is asserted.

In a proper complete-graph edge coloring at odd order n>=3, every nonempty vertex block with no wild edge crossing its boundary has at least three vertices whenever the wild edges are color-connecting.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem wild_odd_color_connecting_closed_block_card_ge_three {n k : ℕ} (hn : 3 ≤ n) (hodd : n%2=1)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (W : Finset (Sym2 (Fin n)))
    (hW : simple_graph_is_color_connecting (⊤ : SimpleGraph (Fin n)) c ↑W)
    (U : Finset (Fin n)) (hU : U.Nonempty)
    (hnocross : ∀ (u v : Fin n) (huv : u ≠ v), u ∈ U → v ∉ U → s(u,v) ∉ W) :
    3 ≤ U.card := by
  classical
  by_contra! hsmall
  have hproper : U ≠ Finset.univ := by
    intro he
    rw [he,Finset.card_univ,Fintype.card_fin] at hsmall
    omega
  have huCard : 1 ≤ U.card := Finset.card_pos.2 hU
  have cross : ∀ (e : (⊤ : SimpleGraph (Fin n)).edgeSet), w279_closed c (c e) U → False := by
    intro e hcl
    obtain ⟨u,v,hne,hu,hv,hw⟩ := wild_color_connecting_crosses_closed_cut c W hW e U hU hproper hcl
    exact hnocross u v hne hu hv hw
  by_cases he : U.card=1
  · obtain ⟨u,rfl⟩ := Finset.card_eq_one.1 he
    obtain ⟨e,he⟩ := wild_kn_exists_missing_color_of_odd hn hodd c u
    apply cross e
    intro a ha b hab hc
    have hau := Finset.mem_singleton.1 ha
    subst a
    exact False.elim (he b hab hc)
  · have he2 : U.card=2 := by omega
    obtain ⟨u,v,hne,rfl⟩ := Finset.card_eq_two.1 he2
    apply cross ⟨s(u,v),wild_kn_mem hne⟩
    intro a ha b hab hc
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha ⊢
    rcases ha with rfl | rfl
    · exact Or.inr (wild_kn_same_color c hab hne hc)
    · have hb : b = u := wild_kn_same_color c hab (Ne.symm hne)
        (hc.trans (w279_c_swap c hne))
      exact Or.inl hb
