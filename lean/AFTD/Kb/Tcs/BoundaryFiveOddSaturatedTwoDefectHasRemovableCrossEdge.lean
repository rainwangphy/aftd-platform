import AFTD.Prelude
import AFTD.Kb.Tcs.FiveOddMixedWitnessIncidenceImpossible
import AFTD.Kb.Tcs.AnticompleteVertexFourDisjointNonneighborSetsBound
import AFTD.Kb.Tcs.FourBlockForbiddenShoreSeparatorBound
import AFTD.Kb.Tcs.BoundaryFiveOddSaturatedTwoDefectRemovableWithIndependence
import AFTD.Kb.Tcs.Op1957MinDegreeForcesMatching
import AFTD.Kb.Tcs.Op1957InducedComplementMinDegree
import AFTD.Kb.Tcs.Op1957ExtendibleIndependenceOfComplementMatching
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# boundary_five_odd_saturated_two_defect_has_removable_cross_edge

Topic: graphs   Node: 8cd46b30d7c3

Provenance: helper lemma. OP-1957: proposed arbitrary odd opposite-block saturated cross-edge reduction.

For every odd c at least seven with c≤k, in the displayed five-by-c four-block graph with the explicit degree, separator, B-block factor-criticality and extendibility assumptions, a first-block vertex adjacent to every other first-block vertex and all of D, with exactly two C nonneighbors, has a removable cross edge.
-/

theorem boundary_five_odd_saturated_two_defect_has_removable_cross_edge
    (k c : ℕ) (hc : 7 ≤ c) (hcodd : Odd c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (hext : is_k_extendable G k) (x p q : Fin (4*k)) (hx : x ∈ A)
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hxp : ¬ G.Adj x p) (hxq : ¬ G.Adj x q)
    (hfull : ∀ y ∈ C, y ≠ p → y ≠ q → G.Adj x y)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d) :
    ∃ y ∈ C, y ≠ p ∧ y ≠ q ∧ is_k_extendable (G.deleteEdges {s(x,y)}) k := by
  classical
  have hind : ∀ I : Finset (Fin (4*k)),
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) → I.card ≤ k := by
    intro U hU
    apply op1957_extendible_independence_of_complement_matching k G hext
    · intro I hI
      have hdegree' : ∀ v, k+I.card ≤ (G.neighborFinset v).card := by
        intro v
        have hh := hdegree v
        omega
      have hcard := Fintype.card_subtype_compl (fun v : Fin (4*k) => v ∈ I)
      simp only [Fintype.card_fin,Fintype.card_coe] at hcard
      have hsize : 2*k ≤ Fintype.card {v : Fin (4*k) // v ∉ I} := by
        rw [hcard]
        omega
      have hdeg := op1957_induced_complement_min_degree G I k hdegree'
      exact op1957_min_degree_forces_matching (G.induce {v | v ∉ I}) k hsize hdeg
    · exact hU
  exact boundary_five_odd_saturated_two_defect_removable_with_independence
    k c hc hcodd hkc G A B C D hAB hAC hAD hBC hBD hCD hcover hA hB hC hD
    hnoAB hnoCD hcritB hdegree hsep hext hind x p q hx hp hq hpq hxp hxq hfull hsatA hsatD
