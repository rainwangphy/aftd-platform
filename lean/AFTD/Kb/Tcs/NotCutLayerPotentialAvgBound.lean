import AFTD.Prelude
import AFTD.Kb.Tcs.CutLayerPotential

/-!
# not_cut_layer_potential_avg_bound

Topic: graphs   Node: 61d5eba1a52e

Provenance: original. Related work: refutes `cut_layer_potential_avg_bound`

The statement `cut_layer_potential_avg_bound` is false: The statement has no hypothesis guaranteeing G.minDegree > 0. When G has an isolated vertex, minDegree = 0, so the right-hand side is 2·(cut count)/0 = 0 in ℝ. A concrete counterexample: V = Fin 2, G = ⊥ (empty graph), X = {1}, x = 0, y = 1. Then x ∈ Xᶜ, y ∈ X, both have no neighbours at all so the "interior" hypotheses hold. We have degree(x) = degree(y) = 0, neighborFinset of each is empty, and minDegree = 0. The left-hand side is 3 − (∑_{\text{empty}} f)/0 + (∑_{\text{empty}} f)/0 = 3 − 0 + 0 = 3, while the right-hand side is 2·|E(X,Xᶜ)|/0 = 2·0/0 = 0. So the claim would assert 3 ≤ 0, which is false. The intended lemma is only true under the additional hypothesis 0 < G.minDegree (equivalently, every vertex has degree at least 1), which is what allows dividing by δ(G). Verified in Lean: the negation of the statement is proved for this instance.
-/

theorem not_cut_layer_potential_avg_bound : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (x y : V)
    (hx : x ∈ (Xᶜ : Finset V)) (hx_no : ∀ u ∈ X, ¬ G.Adj x u)
    (hy : y ∈ X) (hy_no : ∀ w ∈ (Xᶜ : Finset V), ¬ G.Adj y w), let f := cut_layer_potential G X
    (3 - (∑ a ∈ G.neighborFinset x, f a) / (G.degree x : ℝ)
      + (∑ b ∈ G.neighborFinset y, f b) / (G.degree y : ℝ))
      ≤ 2 * ((G.edgeFinset.filter (fun e => ∃ u ∈ X, ∃ v ∈ (Xᶜ : Finset V), e = s(u, v))).card : ℝ) /
          (G.minDegree : ℝ)) := by
  intro h
  have hinst := h (V := Fin 2) (G := (⊥ : SimpleGraph (Fin 2))) (X := ({1} : Finset (Fin 2)))
    (x := 0) (y := 1) (by decide) (by intro u _; simp) (by decide) (by intro w _; simp)
  simp only [SimpleGraph.neighborFinset, SimpleGraph.degree, SimpleGraph.edgeFinset,
    SimpleGraph.neighborSet_bot, Set.toFinset_empty, Finset.card_empty, Finset.sum_empty,
    Nat.cast_zero, zero_div, sub_zero, add_zero,
    SimpleGraph.bot_adj, not_false_eq_true, exists_const, Finset.mem_singleton] at hinst
  norm_num at hinst
