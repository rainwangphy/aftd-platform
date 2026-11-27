import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveOddSaturatedEssentialEdgePatternsWithIndependence
import AFTD.Kb.Tcs.BoundaryFiveOddSaturatedPatternsImpossible
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# boundary_five_odd_saturated_two_defect_removable_with_independence

Topic: graphs   Node: 769de01b8377

Provenance: helper lemma. OP-1957: wire the explicit independence hypothesis into the five-by-odd removable-cross-edge route.

Under the displayed five-by-odd four-block degree, separator, factor-criticality, k-extendibility and independence-number-at-most-k hypotheses, the saturated vertex with exactly two opposite-block nonneighbors has a cross edge whose deletion preserves k-extendibility.
-/

theorem boundary_five_odd_saturated_two_defect_removable_with_independence
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
    (hext : is_k_extendable G k)
    (hind : ∀ I : Finset (Fin (4*k)),
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) → I.card ≤ k)
    (x p q : Fin (4*k)) (hx : x ∈ A)
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hxp : ¬ G.Adj x p) (hxq : ¬ G.Adj x q)
    (hfull : ∀ y ∈ C, y ≠ p → y ≠ q → G.Adj x y)
    (hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a)
    (hsatD : ∀ d ∈ D, G.Adj x d) :
    ∃ y ∈ C, y ≠ p ∧ y ≠ q ∧ is_k_extendable (G.deleteEdges {s(x,y)}) k := by
  classical
  by_contra hn
  apply boundary_five_odd_saturated_patterns_impossible k c hc hkc G A B C D
    hAB hAC hAD hBC hBD hCD hA hB hC hD hnoAB hnoCD hdegree hsep x p q hx hp hq hxp hxq hpq
  intro y hy
  have hyC : y ∈ C := (Finset.mem_sdiff.mp hy).1
  have hnot : y ∉ ({p,q} : Finset (Fin (4*k))) := (Finset.mem_sdiff.mp hy).2
  have hyp : y ≠ p := by intro he; subst y; exact hnot (by simp)
  have hyq : y ≠ q := by intro he; subst y; exact hnot (by simp)
  have hess : ¬ is_k_extendable (G.deleteEdges {s(x,y)}) k := by
    intro he
    exact hn ⟨y,hyC,hyp,hyq,he⟩
  exact boundary_five_odd_saturated_essential_edge_patterns_with_independence
    k c hc hcodd hkc G A B C D hAB hAC hAD hBC hBD hCD hcover hA hB hC hD
    hnoAB hnoCD hcritB hdegree hsep hext hind x p q hx hp hq hpq hxp hxq hfull hsatA hsatD
    y hyC hyp hyq hess
