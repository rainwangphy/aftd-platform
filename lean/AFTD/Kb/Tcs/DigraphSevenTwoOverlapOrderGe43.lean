import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorEdgeLeSumChoose

/-!
# digraph_seven_two_overlap_order_ge_43

Topic: graphs   Node: 383bfcc3d661

Provenance: helper lemma. Order constraint for restricted small-overlap searches in the OP-110 campaign.

A finite digraph with every outdegree at least seven and twice its common-predecessor overlap below its order has at least 43 vertices.
-/

private instance in504_order_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_seven_two_overlap_order_ge_43
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hsmall : 2 * ((∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
      (digraph_common_predecessor_graph D).edgeFinset.card) < Fintype.card α) :
    43 ≤ Fintype.card α := by
  classical
  let n := Fintype.card α
  let S := ∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2
  let E := (digraph_common_predecessor_graph D).edgeFinset.card
  have hES : E ≤ S := digraph_common_predecessor_edge_le_sum_choose α D
  have hS : 21 * n ≤ S := by
    change 21 * Fintype.card α ≤ ∑ v : α,
      Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2
    calc
      21 * Fintype.card α = ∑ _v : α, 21 := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v _
        have h := Nat.choose_le_choose 2 (hdeg v)
        norm_num at h
        exact h
  have hE : E ≤ Nat.choose n 2 :=
    (digraph_common_predecessor_graph D).card_edgeFinset_le_card_choose_two
  have hsmall' : 2 * (S - E) < n := hsmall
  have hlin : 41 * n < 2 * E := by omega
  have hchoose : 2 * Nat.choose n 2 ≤ n * (n - 1) := by
    rw [Nat.choose_two_right]
    have h := Nat.div_mul_le_self (n * (n - 1)) 2
    omega
  have hbound : 2 * E ≤ n * (n - 1) := by omega
  by_contra hn
  have hsub : n - 1 ≤ 41 := by omega
  have hmul : n * (n - 1) ≤ 41 * n := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left n hsub
  omega
