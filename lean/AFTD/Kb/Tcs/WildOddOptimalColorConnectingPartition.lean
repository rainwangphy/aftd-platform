import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCardVerticesLeEdgesAddComponents
import AFTD.Kb.Tcs.WildOddColorConnectingClosedBlockCardGeThree
import AFTD.Kb.Tcs.WildBlockCutOfColorConnecting
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_odd_optimal_color_connecting_partition

Topic: graphs   Node: 1aaf16626ced

Provenance: helper lemma. Structural necessity and certificate-soundness helpers for the OP-306 campaign; arXiv:2610.22142, Sections 3.3.1 and 3.3.2. These make the optimal block-partition route an equivalence at every odd order; no new exact wild-number case or bound is asserted.

At odd order n>=3, every color-connecting edge set of size n-floor(n/3) in a proper complete-graph edge coloring yields a rooted partition into floor(n/3) blocks, each of size at least three, with every used color crossing every nontrivial block cut.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem wild_odd_optimal_color_connecting_partition {n k : ℕ} (hn : 3 ≤ n) (hodd : n%2=1)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (W : Finset (Sym2 (Fin n)))
    (hW : simple_graph_is_color_connecting (⊤ : SimpleGraph (Fin n)) c ↑W)
    (hcard : W.card = n-n/3) :
    ∃ (p : Fin n → Fin (n/3)) (r : Fin (n/3) → Fin n),
      (∀ t, p (r t) = t) ∧
      (∀ t, 3 ≤ ((Finset.univ : Finset (Fin n)).filter fun v => p v = t).card) ∧
      (∀ (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (S : Finset (Fin (n/3))),
        S.Nonempty → S ≠ Finset.univ →
        ∃ (u v : Fin n) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧ c ⟨s(u,v),wild_kn_mem huv⟩ = c e) := by
  classical
  let G : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (↑W : Set (Sym2 (Fin n)))
  have hmin : ∀ C : G.ConnectedComponent, 3 ≤ C.supp.toFinset.card := by
    intro C
    apply wild_odd_color_connecting_closed_block_card_ge_three hn hodd c W hW C.supp.toFinset
    · exact ⟨C.out,Set.mem_toFinset.2 C.out_eq⟩
    · intro u v huv hu hv hw
      have hadj : G.Adj u v := (SimpleGraph.fromEdgeSet_adj (↑W : Set (Sym2 (Fin n)))).2 ⟨Finset.mem_coe.2 hw,huv⟩
      apply hv
      exact Set.mem_toFinset.2 ((C.mem_supp_congr_adj hadj).1 (Set.mem_toFinset.1 hu))
  have hsumV : (∑ C : G.ConnectedComponent, C.supp.toFinset.card) = n := by
    have hi := Finset.card_eq_sum_card_fiberwise (f := G.connectedComponentMk)
      (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset G.ConnectedComponent))
      (fun _ _ => Finset.mem_univ _)
    have hA : ∀ C : G.ConnectedComponent, C.supp.toFinset = Finset.univ.filter (fun v => G.connectedComponentMk v = C) := by
      intro C
      ext v
      simp only [Set.mem_toFinset,SimpleGraph.ConnectedComponent.mem_supp_iff,Finset.mem_filter,Finset.mem_univ,true_and]
    simp_rw [hA]
    simpa only [Finset.card_univ,Fintype.card_fin] using hi.symm
  have hcmin : 3 * Fintype.card G.ConnectedComponent ≤ n := by
    have hi := Finset.sum_le_sum (fun C (_ : C ∈ (Finset.univ : Finset G.ConnectedComponent)) => hmin C)
    simp only [hsumV,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] at hi
    exact_mod_cast hi
  have hEdges : G.edgeFinset.card ≤ W.card := by
    apply Finset.card_le_card
    intro e he
    have he' : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.1 he
    exact (SimpleGraph.edgeSet_fromEdgeSet (↑W : Set (Sym2 (Fin n))) ▸ he').1
  have hcmax : n ≤ Nat.card G.edgeSet + Nat.card G.ConnectedComponent := by
    have hi := simple_graph_card_vertices_le_edges_add_components G
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,Nat.card_fin] using hi
  have hcmin' : 3 * Nat.card G.ConnectedComponent ≤ n := by
    simpa only [← Nat.card_eq_fintype_card] using hcmin
  have hEdges' : Nat.card G.edgeSet ≤ W.card := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hEdges
  have hcc' : Nat.card G.ConnectedComponent = n/3 := by omega
  have hcc : Fintype.card G.ConnectedComponent = n/3 := by simpa only [Nat.card_eq_fintype_card] using hcc' 
  let E : G.ConnectedComponent ≃ Fin (n/3) := Fintype.equivFinOfCardEq hcc
  let p : Fin n → Fin (n/3) := fun v => E (G.connectedComponentMk v)
  let r : Fin (n/3) → Fin n := fun t => (E.symm t).out
  have hr : ∀ t, p (r t) = t := by
    intro t
    change E (G.connectedComponentMk ((E.symm t).out)) = t
    exact (congrArg E (E.symm t).out_eq).trans (E.apply_symm_apply t)
  have hpmin : ∀ t, 3 ≤ ((Finset.univ : Finset (Fin n)).filter fun v => p v = t).card := by
    intro t
    have he : ((Finset.univ : Finset (Fin n)).filter fun v => p v = t) = (E.symm t).supp.toFinset := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_toFinset,SimpleGraph.ConnectedComponent.mem_supp_iff]
      change E (G.connectedComponentMk v) = t ↔ G.connectedComponentMk v = E.symm t
      exact E.apply_eq_iff_eq_symm_apply
    rw [he]
    exact hmin _
  refine ⟨p,r,hr,hpmin,?_⟩
  apply wild_block_cut_of_color_connecting c W hW p r hr
  intro u v huv hw
  apply congrArg E
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ((SimpleGraph.fromEdgeSet_adj (↑W : Set (Sym2 (Fin n)))).2 ⟨Finset.mem_coe.2 hw,huv⟩)
