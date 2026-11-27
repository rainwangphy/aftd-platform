import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleEssentialEdgeAmbientOddShores
import AFTD.Kb.Tcs.BoundaryFiveOddSaturatedEmptyBarrierForcePatterns
import AFTD.Kb.Tcs.BoundaryFiveOddPositiveBarrierForcesPatternsWithExtendibility
import AFTD.Kb.Tcs.NontrivialFactorcriticalGraphConnected

/-!
# boundary_five_odd_saturated_essential_edge_patterns_with_independence

Topic: graphs   Node: 915dc06d899b

Provenance: helper lemma. OP-1957: wire the explicit independence hypothesis through the zero- and positive-barrier cases.

In the displayed four-block graph, with the explicit degree, separator, B-factor-criticality, k-extendibility and independence-number-at-most-k assumptions, every essential cross edge from a saturated vertex with exactly two cross nonneighbors satisfies one of the four displayed defect patterns.
-/

theorem boundary_five_odd_saturated_essential_edge_patterns_with_independence
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
    (hsatD : ∀ d ∈ D, G.Adj x d)
    (y : Fin (4*k)) (hy : y ∈ C) (hyp : y ≠ p) (hyq : y ≠ q)
    (hess : ¬ is_k_extendable (G.deleteEdges {s(x,y)}) k) :
    (∃ r ∈ ({p,q} : Finset (Fin (4*k))), ∃ U ⊆ A.erase x, U.card=2 ∧
      ∀ a ∈ U, ¬ G.Adj a y ∧ ¬ G.Adj a r) ∨
    (∀ a ∈ A.erase x, ¬ G.Adj a y) ∨
    (G.Adj p q ∧ (G.Adj y p ∨ G.Adj y q) ∧
      ∃ U ⊆ B, ∃ Z ⊆ (C \ {p,q,y}), U.card+Z.card=c-4 ∧
        (∀ b ∈ U, ¬ G.Adj b p ∧ ¬ G.Adj b q ∧ ¬ G.Adj b y) ∧
        (∀ z ∈ Z, ¬ G.Adj z p ∧ ¬ G.Adj z q ∧ ¬ G.Adj z y)) ∨
    (¬ G.Adj p q ∧ ¬ G.Adj y p ∧ ¬ G.Adj y q) := by
  classical
  have hB2 : 1 < B.card := by omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hB2
  have hconnB : (G.induce {v | v ∈ B}).Connected :=
    nontrivial_factorcritical_graph_connected (G.induce {v | v ∈ B}) hcritB
      ⟨a,ha⟩ ⟨b,hb⟩ (fun h => hab (congrArg Subtype.val h))
  have hxy : G.Adj x y := hfull y hy hyp hyq
  obtain ⟨X,Y,U,s,hXY,hXU,hYU,hxX,hyY,hoddX,hoddY,hsize,hUodd,hUparity,hcross,hantiX,hantiY⟩ :=
    extendible_essential_edge_ambient_odd_shores k G x y hxy hext hess
  by_cases hz : s = 0
  · have hsize0 : X.card+Y.card+U.card=2*k := by omega
    have hanti : ∀ u ∈ U, ∀ a ∈ X, ¬ G.Adj u a := by
      intro u hu a ha h
      exact hantiX a ha u hu h.symm
    have hh := boundary_five_odd_saturated_empty_barrier_force_patterns
      k c hc hcodd hkc G A B C D hAB hAC hAD hBC hBD hCD hcover hA hB hC hD
      hnoAB hnoCD hconnB hdegree hsep x p q hx hp hq hpq hxp hxq hfull hsatA hsatD
      y hy hyp hyq X Y U hXY hXU hYU hsize0 hxX hyY hoddX hoddY hcross hanti
    rcases hh with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · have hs : 1 ≤ s := by omega
    exact boundary_five_odd_positive_barrier_forces_patterns_with_extendibility
      k c hc hcodd hkc G A B C D hAB hAC hAD hBC hBD hCD hcover hA hB hC hD
      hnoAB hnoCD hcritB hconnB hext hind hdegree hsep x p q y hx hp hq hpq hxp hxq
      hfull hsatA hsatD hy hyp hyq X Y U s hXY hXU hYU hxX hyY hoddX hoddY hs hsize
      hUodd hUparity hcross hantiX hantiY
