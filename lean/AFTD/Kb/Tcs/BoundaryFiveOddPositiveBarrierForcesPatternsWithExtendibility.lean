import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.OddComponentsGroupIntoExactly
import AFTD.Kb.Tcs.TwoExceptionalGroupsAndBlockPool
import AFTD.Kb.Tcs.FiveOddSaturatedSmallShoreArithmeticNoConnectedness
import AFTD.Kb.Tcs.FiveOddSaturatedLargeShoreArithmeticCore
import AFTD.Kb.Tcs.SaturatedOtherShoresOppositeBlockCardLeThree
import AFTD.Kb.Tcs.FourShoreSaturatedYRootCountBound
import AFTD.Kb.Tcs.FourShoreAggregateBlockCriticality
import AFTD.Kb.Tcs.ExtendibleIndependentCommonNonneighborDeficitLeOne
import AFTD.Kb.Tcs.SaturatedSmallShoreSingletonPoolEmpty
import AFTD.Kb.Tcs.EmptyPoolExceptionalShapeArithmetic
import AFTD.Kb.Tcs.BoundaryFiveOddPositiveSmallShoreForcesIndependentTriple
import AFTD.Kb.Tcs.BoundaryFiveOddPositiveLargeShoreForcesCommonDefects
import AFTD.Kb.Tcs.IsKExtendable

/-!
# boundary_five_odd_positive_barrier_forces_patterns_with_extendibility

Topic: graphs   Node: 263ee37d3933

Provenance: helper lemma. OP-1957; positive-separator case of the five-by-odd essential-edge pattern transfer.

The displayed positive-barrier defect patterns hold under the original saturated five-by-odd assumptions together with explicit k-extendibility and independence-number bounds.
-/

theorem boundary_five_odd_positive_barrier_forces_patterns_with_extendibility
    (k c : ℕ) (hc : 7 ≤ c) (hcodd : Odd c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hconnB : (G.induce {v | v ∈ B}).Connected)
    (hext : is_k_extendable G k)
    (hind : ∀ I : Finset (Fin (4*k)),
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) → I.card ≤ k)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (x p q y : Fin (4*k)) (hxA : x ∈ A) (hp : p ∈ C) (hq : q ∈ C)
    (hpq : p ≠ q) (hxp : ¬ G.Adj x p) (hxq : ¬ G.Adj x q)
    (hfull : ∀ z ∈ C, z ≠ p → z ≠ q → G.Adj x z)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d)
    (hyC : y ∈ C) (hyp : y ≠ p) (hyq : y ≠ q)
    (X Y U : Finset (Fin (4*k))) (s : ℕ)
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hxX : x ∈ X) (hyY : y ∈ Y) (hoddX : Odd X.card) (hoddY : Odd Y.card)
    (hs : 1 ≤ s) (hsize : X.card+Y.card+U.card+s=2*k)
    (hUodd : s ≤ (G.induce {v | v ∈ U}).oddComponents.ncard)
    (hUparity : U.card % 2 = s % 2)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hantiX : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hantiY : ∀ b ∈ Y, ∀ u ∈ U, ¬ G.Adj b u) :
    (∃ r ∈ ({p,q} : Finset (Fin (4*k))), ∃ T ⊆ A.erase x, T.card=2 ∧
      ∀ a ∈ T, ¬ G.Adj a y ∧ ¬ G.Adj a r) ∨
    (∀ a ∈ A.erase x, ¬ G.Adj a y) ∨
    (G.Adj p q ∧ (G.Adj y p ∨ G.Adj y q) ∧
      ∃ T ⊆ B, ∃ Z ⊆ (C \ {p,q,y}), T.card+Z.card=c-4 ∧
        (∀ b ∈ T, ¬ G.Adj b p ∧ ¬ G.Adj b q ∧ ¬ G.Adj b y) ∧
        (∀ z ∈ Z, ¬ G.Adj z p ∧ ¬ G.Adj z q ∧ ¬ G.Adj z y)) ∨
    (¬ G.Adj p q ∧ ¬ G.Adj y p ∧ ¬ G.Adj y q) := by
  by_cases hsmall : (X ∩ A).card ≤ 2
  · exact Or.inr (Or.inr (Or.inr (boundary_five_odd_positive_small_shore_forces_independent_triple
      k c hc hcodd hkc G A B C D hAB hAC hAD hBC hBD hCD hcover hA hB hC hD hnoAB hnoCD
      hcritB hconnB hext hind hdegree hsep x p q y hxA hp hq hpq hxp hxq hfull hsatA hsatD
      hyC hyp hyq X Y U s hXY hXU hYU hxX hyY hoddX hoddY hs hsize hUodd hUparity hcross hantiX hantiY hsmall)))
  · have hlarge : 3 ≤ (X ∩ A).card := by omega
    rcases boundary_five_odd_positive_large_shore_forces_common_defects
      k c hc hcodd hkc G A B C D hAB hAC hAD hBC hBD hCD hcover hA hB hC hD hnoAB hnoCD
      hcritB hconnB hext hind hdegree hsep x p q y hxA hp hq hpq hxp hxq hfull hsatA hsatD
      hyC hyp hyq X Y U s hXY hXU hYU hxX hyY hoddX hoddY hs hsize hUodd hUparity hcross hantiX hantiY hlarge with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
