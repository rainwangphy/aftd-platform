import AFTD.Prelude

/-!
# op309_connected_class_degree_cycle_identity

Topic: graphs   Node: a01f53d7d913

Provenance: helper lemma. OP-309 high-girth overlap-peeling density reduction, IN-1099.

In a connected graph with all degrees between one and three, twice its cycle rank plus its number of degree-one vertices equals two plus its number of degree-three vertices.
-/

theorem op309_connected_class_degree_cycle_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, 1 ≤ H.degree v ∧ H.degree v ≤ 3)
    (hconn : H.Connected) :
    2 * (H.edgeFinset.card + 1 - Fintype.card V) +
      (Finset.univ.filter fun v => H.degree v = 1).card =
      2 + (Finset.univ.filter fun v => H.degree v = 3).card := by
  classical
  have hs : (∑ v, (H.degree v + if H.degree v = 1 then 1 else 0)) =
      ∑ v, (2 + if H.degree v = 3 then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro v hv
    have hd := hdeg v
    split_ifs <;> omega
  have hs' : (∑ v, H.degree v) + (Finset.univ.filter fun v => H.degree v = 1).card =
      2 * Fintype.card V + (Finset.univ.filter fun v => H.degree v = 3).card := by
    simpa [Finset.sum_add_distrib, ← Finset.sum_filter, Nat.mul_comm] using hs
  have hh := H.sum_degrees_eq_twice_card_edges
  have hcard : Fintype.card V ≤ H.edgeFinset.card + 1 := by
    simpa [Nat.card_eq_fintype_card, ← H.edgeFinset_card] using hconn.card_vert_le_card_edgeSet_add_one
  omega
