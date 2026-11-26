import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteSubsetHasMaximumMatching
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingSymmetryOfIndependence
import AFTD.Kb.Tcs.ExtendibleEqualCutMaximumMatchingDeficiencyAtMostOne
import AFTD.Kb.Tcs.FiniteMatchingHasSubmatchingOfEachSmallerSize
import AFTD.Kb.Tcs.ExtendibleBalancedCutMatchingDeficiencyOddBound
import AFTD.Kb.Tcs.ExtendibleBalancedCutOddBoundOfNearPerfectHypothesis
import AFTD.Kb.Tcs.IsKExtendable

/-!
# extendible_high_degree_balanced_cut_odd_component_bound

Topic: graphs   Node: efd409bf00d6

Provenance: helper lemma. Balanced-cut reduction for OP-1957; https://arxiv.org/abs/1011.3384.

Under the displayed extendibility, separator, degree and independence assumptions, each balanced cut has at most two odd components on the opposite side.
-/

theorem extendible_high_degree_balanced_cut_odd_component_bound
    (k : ℕ) (hk : 1 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (hind : ∀ I : Finset (Fin (4*k)),
      (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) → I.card ≤ k)
    (C : Finset (Fin (4*k))) (hcard : C.card = 2*k) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ 2 := by
  set_option maxHeartbeats 4000000 in
    classical
    apply extendible_balanced_cut_odd_bound_of_near_perfect_hypothesis k hk G hext hsep hdegree hind C hcard
    intro M N hM hN hMC hNC hmaxM hmaxN heq
    exact extendible_equal_cut_maximum_matching_deficiency_at_most_one k G hext hdegree C hcard M N hM hN hMC hNC hmaxM hmaxN heq hind
