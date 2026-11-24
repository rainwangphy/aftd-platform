import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveOddSaturatedIncidenceBudgets
import AFTD.Kb.Tcs.FiveOddMixedWitnessIncidenceImpossible

/-!
# boundary_five_odd_saturated_patterns_impossible

Topic: graphs   Node: e55b5eb078b8

Provenance: helper lemma. OP-1957, saturated five-by-odd block route

The degree, separator and four-block hypotheses rule out the listed mixed essential-edge witness pattern holding at every opposite-block vertex other than the two distinguished nonneighbors.
-/

set_option maxHeartbeats 4000000

theorem boundary_five_odd_saturated_patterns_impossible (k c : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj] (A B C D : Finset (Fin (4*k))) (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D) (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D) (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c) (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b) (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card) (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty → Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ → (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card) (x p q : Fin (4*k)) (hx : x ∈ A) (hp : p ∈ C) (hq : q ∈ C) (hxp : ¬ G.Adj x p) (hxq : ¬ G.Adj x q)
    (hpq : p ≠ q)
    (hpatterns : ∀ y ∈ C \ {p,q},
      (∃ r ∈ ({p,q} : Finset (Fin (4*k))), ∃ U ⊆ A.erase x, U.card=2 ∧
        ∀ a ∈ U, ¬ G.Adj a y ∧ ¬ G.Adj a r) ∨
      (∀ a ∈ A.erase x, ¬ G.Adj a y) ∨
      (G.Adj p q ∧ (G.Adj y p ∨ G.Adj y q) ∧
        ∃ U ⊆ B, ∃ Z ⊆ (C \ {p,q,y}), U.card+Z.card=c-4 ∧
          (∀ b ∈ U, ¬ G.Adj b p ∧ ¬ G.Adj b q ∧ ¬ G.Adj b y) ∧
          (∀ z ∈ Z, ¬ G.Adj z p ∧ ¬ G.Adj z q ∧ ¬ G.Adj z y)) ∨
      (¬ G.Adj p q ∧ ¬ G.Adj y p ∧ ¬ G.Adj y q)) : False := by
  classical
  obtain ⟨hrows,hcols,hcut⟩ := boundary_five_odd_saturated_incidence_budgets
    k c hc hkc G A B C D hAB hAC hAD hBC hBD hCD hA hB hC hD
    hnoAB hnoCD hdegree hsep x p q hx hp hq hxp hxq
  have hA4 : (A.erase x).card = 4 := by rw [Finset.card_erase_of_mem hx,hA]
  have hC7 : 7 ≤ C.card := by omega
  apply five_odd_mixed_witness_incidence_impossible (A.erase x) B C
    (fun a y => ¬ G.Adj a y) (fun b y => ¬ G.Adj b y) (fun y z => ¬ G.Adj y z)
    hA4 hC7 p q hp hq hpq
  · intro u v h huv
    exact h huv.symm
  · exact hrows
  · simpa [hC] using hcols
  · simpa [hC] using hcut
  · intro y hy
    have hh := hpatterns y hy
    simpa only [not_not, hC] using hh
