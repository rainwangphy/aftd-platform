import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957OneDefectCriticalityNumericTransfer
import AFTD.Kb.Tcs.Op1957OneDefectCriticalityGeneralNumericTransfer
import AFTD.Kb.Tcs.Op1957TwoDefectsForceOneOutsideGroup
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# op1957_one_defect_factorcritical_two_numeric_bounds

Topic: graphs   Node: 76e29edf47d2

Provenance: helper lemma. OP-1957: one-defect boundary graph-to-count transfer, arXiv:2611.22690

Under the displayed four-block degree, factor-criticality and anticompleteness assumptions, the general one-defect factor-critical inequality holds; if the pool meets the five-vertex block, the sharper single-exception parity inequality also holds.
-/

theorem op1957_one_defect_factorcritical_two_numeric_bounds
    {I : Type*} [DecidableEq I] (k : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D X Y : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hsizeAB : A.card+B.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hcrit : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (K : Finset I) (T : I → Finset (Fin (4*k)))
    (hXY : Disjoint X Y)
    (hXT : ∀ i ∈ K, Disjoint X (T i)) (hYT : ∀ i ∈ K, Disjoint Y (T i))
    (hTT : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (T i) (T j))
    (hantiXY : ∀ u ∈ X ∩ B, ∀ v ∈ Y ∩ B, ¬ G.Adj u v)
    (hantiXT : ∀ i ∈ K, ∀ u ∈ X, ∀ v ∈ T i, ¬ G.Adj u v)
    (hantiYT : ∀ i ∈ K, ∀ u ∈ Y, ∀ v ∈ T i, ¬ G.Adj u v)
    (hantiTT : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j, ¬ G.Adj u v)
    (hYB : (Y ∩ B).Nonempty) (hoddT : ∀ i ∈ K, Odd (T i).card)
    (x y : Fin (4*k)) (hxA : x ∈ A) (hyC : y ∈ C) (hxX : x ∈ X) (hyY : y ∈ Y) :
    let U := K.biUnion T
    (K.card + (if (X ∩ B).card%2=1 then 1 else 0) +
      (X ∩ B).card+(Y ∩ B).card+(U ∩ B).card+5 ≤
      2*k + (U ∩ A).card+(U ∩ C).card+(U ∩ D).card) ∧
    ((U ∩ A).Nonempty →
      K.card + (if ((U ∩ A).card+(U ∩ C).card+(U ∩ D).card)%2=0 then 1 else 0) +
      (if (X ∩ B).card%2=1 then 1 else 0) +
      (X ∩ B).card+(Y ∩ B).card+(U ∩ B).card+4 ≤ 2*k) := by
  classical
  let U := K.biUnion T
  have hB : B.card+5=2*k := by omega
  refine ⟨?_,?_⟩
  · exact op1957_one_defect_criticality_general_numeric_transfer G A B C D X Y
      hAB hAC hAD hBC hBD hCD hcover k hB K T hcrit hXY hXT hYT hTT
      hantiXY hantiXT hantiYT hantiTT hYB hoddT
  · intro hUA
    obtain ⟨w,hw⟩ := hUA
    have hwU := (Finset.mem_inter.mp hw).1
    have hwA := (Finset.mem_inter.mp hw).2
    obtain ⟨j,hj,hwT⟩ := Finset.mem_biUnion.mp hwU
    have hwB : w ∉ B := fun h => Finset.disjoint_left.mp hAB hwA h
    have hxB : x ∉ B := fun h => Finset.disjoint_left.mp hAB hxA h
    have hyB : y ∉ B := fun h => Finset.disjoint_left.mp hBC h hyC
    have hxw : x ≠ w := by
      intro he; subst x
      exact Finset.disjoint_left.mp (hXT j hj) hxX hwT
    have hyw : y ≠ w := by
      intro he; subst y
      exact Finset.disjoint_left.mp (hYT j hj) hyY hwT
    have hxy : x ≠ y := by
      intro he; subst x
      exact Finset.disjoint_left.mp hAC hxA hyC
    have hnx : ¬ G.Adj w x := fun h => hantiXT j hj x hxX w hwT h.symm
    have hny : ¬ G.Adj w y := fun h => hantiYT j hj y hyY w hwT h.symm
    have hxT : ∀ i ∈ K, x ∉ T i := by
      intro i hi hx
      exact Finset.disjoint_left.mp (hXT i hi) hxX hx
    have hyT : ∀ i ∈ K, y ∉ T i := by
      intro i hi hy
      exact Finset.disjoint_left.mp (hYT i hi) hyY hy
    have hsize : Fintype.card (Fin (4*k)) = B.card+(2*k+4)+1 := by
      simp only [Fintype.card_fin]
      omega
    have hdegree' : 2*k+4 ≤ (G.neighborFinset w).card+2 := by have hh := hdegree w; omega
    have hother := op1957_two_defects_force_one_outside_group G B (2*k+4) hsize K T j hj
      hantiTT w x y hwT hwB (hnoAB w hwA) hdegree' hxB hyB hxw hyw hxy hnx hny hxT hyT hTT
    exact op1957_one_defect_criticality_numeric_transfer G A B C D X Y
      hAB hAC hAD hBC hBD hCD hcover k hB K T hcrit hXY hXT hYT hTT
      hantiXY hantiXT hantiYT hantiTT hYB hoddT j hj (fun i hi hij => hother i hi hij.symm)
