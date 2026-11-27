import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957OddComponentsAmbientPartition
import AFTD.Kb.Tcs.SaturatedBarrierGroupsOutsideBAtMostTwo
import AFTD.Kb.Tcs.FiveOddSaturatedLargeShoreAggregatePattern
import AFTD.Kb.Tcs.FourShoreSaturatedYRootCountBound
import AFTD.Kb.Tcs.FourShoreAggregateBlockCriticality
import AFTD.Kb.Tcs.Op1957LargeShoreReductionToBOnly
import AFTD.Kb.Tcs.BoundaryFiveOddLargeShoreBOnlyPositiveBarrierImpossible
import AFTD.Kb.Tcs.BoundaryFiveOddSaturatedTwoOddShoresForcePatterns
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# boundary_five_odd_positive_large_shore_forces_common_defects

Topic: graphs   Node: 2b098bba3f77

Provenance: helper lemma. OP-1957: large-shore positive-barrier assembly under the stated degree and separator hypotheses.

Under the displayed saturated five-by-odd partition, extendibility, independence, degree and separator hypotheses, a positive barrier whose x-shore meets A in at least three vertices yields either two common A-block defects or no y-neighbors among the four A vertices besides x.
-/

theorem boundary_five_odd_positive_large_shore_forces_common_defects
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
    (hantiY : ∀ b ∈ Y, ∀ u ∈ U, ¬ G.Adj b u)
    (hlarge : 3 ≤ (X ∩ A).card) :
    (∃ r ∈ ({p,q} : Finset (Fin (4*k))), ∃ T ⊆ A.erase x, T.card=2 ∧
      ∀ a ∈ T, ¬ G.Adj a y ∧ ¬ G.Adj a r) ∨
    (∀ a ∈ A.erase x, ¬ G.Adj a y) := by
  classical
  have hanti : ∀ u ∈ U, ¬ G.Adj x u := fun u hu => hantiX x hxX u hu
  have hregion : Y ∪ U ⊆ B ∪ {p,q,y} :=
    in1159_saturated_other_shores_subset G A B C D X Y U x y p q
      hAC hCD hcover hxX hyC hXY hXU hcross hanti hsatA hsatD hfull
  apply op1957_large_shore_reduction_to_B_only G A B X Y U x y p q hxA hxX hyY hYU hA
    hcross hantiX hregion hlarge
  intro hY hU hle
  exact boundary_five_odd_large_shore_B_only_positive_barrier_impossible k c hc hkc G A B C D X Y U
    hAB hAC hAD hBC hBD hCD hcover hA hB hC hD hnoAB hnoCD hcritB hconnB hdegree hsep
    x y hxA hyC hxX hyY hXY hXU hYU hY hU s hs hsize hUodd hUparity hcross hantiX hantiY ⟨hlarge,hle⟩
