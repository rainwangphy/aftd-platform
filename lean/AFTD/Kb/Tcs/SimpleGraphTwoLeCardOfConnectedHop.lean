import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_two_le_card_of_connected_hop

Topic: graphs   Node: 0af502933cac

Provenance: helper lemma. arXiv:2610.18463, Section 1

Every connected simple graph on a finite vertex set that admits a hop has at least two vertices.
-/

/-- Every connected finite simple graph admitting a hop has at least two vertices. -/
theorem simple_graph_two_le_card_of_connected_hop {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (h : Equiv.Perm V)
    (hh : simple_graph_is_hop G h) :
    2 ≤ Fintype.card V := by
  by_contra hlt
  have hle : Fintype.card V ≤ 1 := by omega
  obtain ⟨v⟩ := hconn.nonempty
  have hv : h v = v := (Fintype.card_le_one_iff.mp hle) (h v) v
  have hvv : G.Adj v v := by simpa [hv] using hh v
  exact SimpleGraph.irrefl G hvv
