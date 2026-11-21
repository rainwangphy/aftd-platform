import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.NontrivialFactorcriticalGraphConnected
import AFTD.Kb.Tcs.ConnectedDeletionMatchesIfAllOtherDeletionsMatch
import AFTD.Kb.Tcs.PerfectMatchingTwinsSwitchPartner
import AFTD.Kb.Tcs.ConnectedGraphDeleteTwinWithCommonNeighborConnected

/-!
# factorcritical_twins_forced_edge_is_bridge

Topic: graphs   Node: 73e798b3966f

Provenance: helper lemma. OP-1957; common generalization of the proved false-twin forced-edge bridge lemma and the adjacent-twin switch, supported by experiment 37003.

In a finite 1-factor-critical graph, if two distinct vertices have identical neighborhoods outside the pair, any forced matching edge incident to one is a bridge after deleting the other. The twins may be adjacent or nonadjacent.
-/

theorem factorcritical_twins_forced_edge_is_bridge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hcrit : is_k_factor_critical G 1) (x y z : V) (hxy : x ≠ y) (htwin : ∀ a, a ≠ x → a ≠ y → (G.Adj x a ↔ G.Adj y a)) (hyz : z ≠ y) (hxz : G.Adj x z) (hforced : ¬ ∃ P : ((G.induce {a | a ≠ y}).deleteEdges {s(⟨x,hxy⟩,⟨z,hyz⟩)}).Subgraph, P.IsPerfectMatching) : ¬ ((G.induce {a | a ≠ y}).deleteEdges {s(⟨x,hxy⟩,⟨z,hyz⟩)}).Reachable ⟨x,hxy⟩ ⟨z,hyz⟩ := by
  classical
  intro hreach
  let F := G.deleteEdges {s(x,z)}
  have hzy : z ≠ y := hyz
  have hzx : z ≠ x := hxz.ne.symm
  have hyzG : G.Adj y z := (htwin z hzx hzy).mp hxz
  have hconn : (G.induce {a | a ≠ y}).Connected :=
    connected_graph_delete_twin_with_common_neighbor_connected G (nontrivial_factorcritical_graph_connected G hcrit x y hxy) x y z hxy hxz hyzG htwin
  have hconn' := hconn.connected_delete_edge_of_not_isBridge (x := ⟨x,hxy⟩) (y := ⟨z,hyz⟩)
    (by rw [SimpleGraph.isBridge_iff]; exact not_not.mpr hreach)
  have heq : (F.induce {a | a ≠ y}) = ((G.induce {a | a ≠ y}).deleteEdges
      {s(⟨x,hxy⟩,⟨z,hyz⟩)}) := by
    ext a b
    simp only [F, SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff, Subtype.ext_iff]
  have hFconn : (F.induce {a | a ≠ y}).Connected := by rw [heq]; exact hconn'
  have hother : ∀ b : V, b ≠ y → ∃ P : (F.induce {v | v ≠ b}).Subgraph, P.IsPerfectMatching := by
    intro b hby
    have hm := hcrit {b} (by simp)
    have hs : (↑({b} : Finset V) : Set V)ᶜ = {v | v ≠ b} := by
      ext v
      simp
    have hm' : ∃ P : (G.induce {v | v ≠ b}).Subgraph, P.IsPerfectMatching := by
      rw [← hs]
      exact hm
    obtain ⟨P, hP⟩ := hm'
    have hQ : ∃ Q : (G.induce {v | v ≠ b}).Subgraph, Q.IsPerfectMatching ∧
        ∀ a c, Q.Adj a c → s(a.val,c.val) ≠ s(x,z) := by
      by_cases hbx : b = x
      · subst b
        refine ⟨P, hP, ?_⟩
        intro a c hac he
        rcases Sym2.eq_iff.mp he with ⟨ha,hc⟩ | ⟨ha,hc⟩
        · exact a.property ha
        · exact c.property hc
      · by_cases hbz : b = z
        · subst b
          refine ⟨P, hP, ?_⟩
          intro a c hac he
          rcases Sym2.eq_iff.mp he with ⟨ha,hc⟩ | ⟨ha,hc⟩
          · exact c.property hc
          · exact a.property ha
        · have hxb : x ≠ b := fun h => hbx h.symm
          have hyb : y ≠ b := hby.symm
          have hzb : z ≠ b := fun h => hbz h.symm
          have hxy' : (⟨x,hxb⟩ : {v : V // v ≠ b}) ≠ ⟨y,hyb⟩ := by
            intro h
            exact hxy (congrArg Subtype.val h)
          have htwin' : ∀ a : {v : V // v ≠ b}, a ≠ ⟨x,hxb⟩ → a ≠ ⟨y,hyb⟩ →
              ((G.induce {v | v ≠ b}).Adj ⟨x,hxb⟩ a ↔
                (G.induce {v | v ≠ b}).Adj ⟨y,hyb⟩ a) := by
            intro a hax hay
            change G.Adj x a.val ↔ G.Adj y a.val
            apply htwin a.val
            · intro he; apply hax; exact Subtype.ext he
            · intro he; apply hay; exact Subtype.ext he
          have hzy' : (⟨z,hzb⟩ : {v : V // v ≠ b}) ≠ ⟨y,hyb⟩ := by
            intro he; exact hyz (congrArg Subtype.val he)
          have hQ' : ∃ Q : (G.induce {v | v ≠ b}).Subgraph,
              Q.IsPerfectMatching ∧ ¬ Q.Adj ⟨x,hxb⟩ ⟨z,hzb⟩ := by
            by_cases hp : P.Adj ⟨x,hxb⟩ ⟨z,hzb⟩
            · exact perfect_matching_twins_switch_partner _ P hP _ _ _ hxy' hzy' htwin' hp
            · exact ⟨P, hP, hp⟩
          obtain ⟨Q, hmatch, hno⟩ := hQ'
          refine ⟨Q, hmatch, ?_⟩
          intro a c hac he
          rcases Sym2.eq_iff.mp he with ⟨ha,hc⟩ | ⟨ha,hc⟩
          · have ha' : a = ⟨x,hxb⟩ := Subtype.ext ha
            have hc' : c = ⟨z,hzb⟩ := Subtype.ext hc
            exact hno (ha' ▸ hc' ▸ hac)
          · have ha' : a = ⟨z,hzb⟩ := Subtype.ext ha
            have hc' : c = ⟨x,hxb⟩ := Subtype.ext hc
            exact hno (hc' ▸ ha' ▸ hac.symm)
    obtain ⟨Q, hmatch, havoid⟩ := hQ
    have hle : Q.spanningCoe ≤ F.induce {v | v ≠ b} := by
      intro a c hac
      change F.Adj a.val c.val
      exact SimpleGraph.deleteEdges_adj.mpr ⟨Q.adj_sub hac, by simpa using havoid a c hac⟩
    exact ⟨SimpleGraph.toSubgraph (G := F.induce {v | v ≠ b}) Q.spanningCoe hle, (SimpleGraph.Subgraph.IsPerfectMatching.toSubgraph_iff hle).mpr hmatch⟩
  have hmatch := connected_deletion_matches_if_all_other_deletions_match F y hFconn hother
  rw [heq] at hmatch
  exact hforced hmatch
