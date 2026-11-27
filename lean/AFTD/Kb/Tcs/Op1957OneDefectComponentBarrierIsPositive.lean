import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957OneDefectEmptyBarrierImpossible
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# op1957_one_defect_component_barrier_is_positive

Topic: graphs   Node: 5676ba0d7c73

Provenance: helper lemma. OP-1957 one-defect barrier reduction

Under the displayed five-by-odd degree, separator, factor-criticality and one-defect hypotheses, any component-barrier decomposition with a small first shore has positive barrier size.
-/

theorem op1957_one_defect_component_barrier_is_positive
    {ι : Type*} [DecidableEq ι] (k c : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D X Y S : Finset (Fin (4*k))) (I : Finset ι) (T : ι → Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (x y : Fin (4*k)) (hxA : x ∈ A) (hyC : y ∈ C) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hXY : Disjoint X Y) (hS : S.card=I.card)
    (hres : (X ∪ Y ∪ I.biUnion T ∪ S).card=2*k)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hdefect : (C.filter (fun w => ¬ G.Adj x w)).card ≤ 1)
    (hsmallA : (X ∩ A).card ≤ 2) : 1 ≤ I.card := by
  classical
  by_contra hn
  have hIcard : I.card=0 := by omega
  have hI : I=∅ := Finset.card_eq_zero.mp hIcard
  have hScard : S.card=0 := by omega
  have hS0 : S=∅ := Finset.card_eq_zero.mp hScard
  have hsize : X.card+Y.card=2*k := by
    simpa [hI,hS0,Finset.card_union_of_disjoint hXY] using hres
  exact op1957_one_defect_empty_barrier_impossible k c hc hkc G A B C D X Y
    hAB hAC hAD hBC hBD hCD hcover hA hB hC hD hnoAB hnoCD hcritB hdegree hsep
    x y hxA hyC hxX hyY hXY hsize hcross hdefect hsmallA
