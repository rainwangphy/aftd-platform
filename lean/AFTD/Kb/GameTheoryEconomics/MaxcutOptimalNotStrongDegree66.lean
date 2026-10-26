import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalStrongUpToDegree
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeGraph
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeInitialColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeStableColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutAnchorThreeInitialOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.Tcs.V

/-!
# maxcut_optimal_not_strong_degree_66

Topic: equilibria   Node: 7e648dc27b42

Provenance: formalization of a published result. Source: arXiv:2610.04948, Theorem 2 for k = 3, with the degree bound read off the construction G_3 of Sec. 2.1 (the paper does not state the degree); the upper-bound side of list entry OP-86, a question proposed here from Corollary 9 (the known bound Δ ≤ 2k − 1 of Carosi et al., which the paper recovers).

There is a finite simple graph of maximum degree at most 66 with an optimal coloring of the Max-3-Cut game that is not a strong equilibrium; hence Δ*(3) ≤ 65. (The graph G_3 of arXiv:2610.04948, Sec. 2, has 91 vertices and maximum degree 66, attained by the anchor vertices r_{3,1}.)
-/

open scoped BigOperators
namespace MaxcutDegree66Check
private abbrev V := Fin 16 ⊕ (Fin 3 × Fin 25)
private abbrev G := maxcut_anchor_three_graph
private instance graph_decidable : DecidableRel G.Adj := by
  unfold G maxcut_anchor_three_graph
  infer_instance
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000
private lemma anchor_adj (j l : Fin 3) (i t : Fin 25) :
    G.Adj (.inr (j,i)) (.inr (l,t)) ↔ j ≠ l := by
  change ((Sum.inr (j,i) : V) ≠ Sum.inr (l,t) ∧ (j ≠ l ∨ l ≠ j)) ↔ j ≠ l
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro heq
    exact h (congrArg Prod.fst (Sum.inr.inj heq))
private lemma degree_bound : ∀ v, G.degree v ≤ 66 := by
  have hcore : ∀ u : Fin 16, G.degree (Sum.inl u) ≤ 66 := by decide
  intro v
  cases v with
  | inl u => exact hcore u
  | inr a =>
    rcases a with ⟨j,i⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
      Finset.card_filter, Fintype.sum_sum_type]
    have ha : (∑ w : Fin 3 × Fin 25,
        if G.Adj (.inr (j,i)) (.inr w) then 1 else 0) = 50 := by
      rw [Fintype.sum_prod_type]
      simp_rw [anchor_adj]
      fin_cases j <;> decide
    have hb : (∑ u : Fin 16,
        if G.Adj (.inr (j,i)) (.inl u) then 1 else 0) ≤ 16 := by
      calc
        _ ≤ ∑ _u : Fin 16, 1 := Finset.sum_le_sum (fun u _ => by split_ifs <;> omega)
        _ = 16 := by decide
    rw [ha]
    omega

private lemma deviation : is_maxcut_strong_deviation G
    maxcut_anchor_three_initial_coloring
    (Finset.univ.filter fun v : V => v.isLeft)
    maxcut_anchor_three_stable_coloring := by
  unfold is_maxcut_strong_deviation
  decide
end MaxcutDegree66Check

theorem maxcut_optimal_not_strong_degree_66 : ¬ maxcut_optimal_strong_up_to_degree 3 66 := by
  intro h
  have hs := h (Fin 16 ⊕ (Fin 3 × Fin 25)) maxcut_anchor_three_graph
    MaxcutDegree66Check.degree_bound maxcut_anchor_three_initial_coloring maxcut_anchor_three_initial_optimal
  exact hs _ _ MaxcutDegree66Check.deviation
