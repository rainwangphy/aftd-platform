import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedMatchingEdgeBlocksFourAndSixSwitches

/-!
# perfect_matching_twins_switch_partner

Topic: graphs   Node: 2d9397bee05c

Provenance: helper lemma. OP-1957: extension of the false-twin bridge route to adjacent and nonadjacent twins.

Any matching edge incident to one of two distinct vertices with identical neighbors outside the pair can be avoided by another perfect matching, provided the edge does not join the pair.
-/

theorem perfect_matching_twins_switch_partner {V : Type*} (G : SimpleGraph V)
    (P : G.Subgraph) (hP : P.IsPerfectMatching) (x y z : V)
    (hxy : x ≠ y) (hzy : z ≠ y)
    (htwin : ∀ a, a ≠ x → a ≠ y → (G.Adj x a ↔ G.Adj y a))
    (hxz : P.Adj x z) :
    ∃ Q : G.Subgraph, Q.IsPerfectMatching ∧ ¬ Q.Adj x z := by
  classical
  by_contra hno
  have hforced : ∀ Q : G.Subgraph, Q.IsPerfectMatching → Q.Adj x z := by
    intro Q hQ
    by_contra hn
    exact hno ⟨Q,hQ,hn⟩
  obtain ⟨w, hyw, _⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) y
  have hxzG : G.Adj x z := P.adj_sub hxz
  have hywG : G.Adj y w := P.adj_sub hyw
  have hzx : z ≠ x := hxzG.ne.symm
  have hwy : w ≠ y := hywG.ne.symm
  have hwx : w ≠ x := by
    intro h
    subst w
    have he : z = y := hP.1.eq_of_adj_left hxz hyw.symm
    exact hzy he
  have hwz : w ≠ z := by
    intro h
    subst w
    have he : x = y := hP.1.eq_of_adj_left hxz.symm hyw.symm
    exact hxy he
  have hinj : Function.Injective (![x,z,y,w] : Fin 4 → V) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hyz : G.Adj y z := (htwin z hzx hzy).mp hxzG
  have hxw : G.Adj x w := (htwin w hwx hwy).mpr hywG
  exact (forced_matching_edge_blocks_four_and_six_switches G P hP x z hxz hforced).1
    ⟨y,w,hinj,hyw,hyz.symm,hxw⟩
