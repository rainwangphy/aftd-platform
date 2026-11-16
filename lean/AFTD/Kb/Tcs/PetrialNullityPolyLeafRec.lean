import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialNullityPoly
import AFTD.Kb.Tcs.PetrialNullityPolyCoeffEqPetrialCoeff
import AFTD.Kb.Tcs.PetrialMatrixRankLeCard
import AFTD.Kb.Tcs.PetrialLeafFlipBijective
import AFTD.Kb.Tcs.PetrialLeafRestrictionBijective
import AFTD.Kb.Tcs.PetrialLeafOnePivot
import AFTD.Kb.Tcs.PetrialLeafZeroPivot
import AFTD.Kb.Tcs.PetrialMatrix
import AFTD.Kb.Tcs.PetrialLeafRestriction
import AFTD.Kb.Tcs.PetrialLeafFlip

/-!
# petrial_nullity_poly_leaf_rec

Topic: combinatorics   Node: 1f46e11be277

Provenance: helper lemma. step towards op_1239_max_degree_three_tree_petrial_log_concave

For a finite graph G with a degree-one vertex v whose neighbour is u, the nullity generating polynomial of G equals the nullity generating polynomial of G with v deleted, plus twice the nullity generating polynomial of G with u and v deleted.
-/

open Polynomial
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Leaf-elimination recursion: if v is a vertex of degree 1 with neighbour u, the nullity polynomial satisfies p(G) = p(G - v) + 2 * p(G - {u,v}). -/
theorem petrial_nullity_poly_leaf_rec {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] {v u : V}
    (hv : T.degree v = 1) (hu : T.Adj v u) :
    petrial_nullity_poly T
      = petrial_nullity_poly (T.induce ({v}ᶜ : Set V))
        + 2 * petrial_nullity_poly (T.induce (({u} ∪ {v})ᶜ : Set V)) := by
  classical
  have hvu : v ≠ u := T.ne_of_adj hu
  have huv : u ≠ v := hvu.symm
  obtain ⟨w, hw, hwuniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
  have huniq : ∀ z, T.Adj v z → z = u := by
    intro z hz
    exact (hwuniq z hz).trans (hwuniq u hu).symm
  have hc1 : Fintype.card V = 1 + Fintype.card (({v}ᶜ : Set V)) := by
    have h := Fintype.card_congr (Equiv.Set.sumCompl ({v} : Set V))
    simp only [Fintype.card_sum] at h
    have hc : Fintype.card ({v} : Set V) = 1 := by simp
    omega
  have hc2 : Fintype.card V = 2 + Fintype.card (({u, v}ᶜ : Set V)) := by
    let P : Set V := {u, v}
    let f : Fin 2 → P := fun i => if i = 0 then ⟨v, by simp [P]⟩ else ⟨u, by simp [P]⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j h
        fin_cases i <;> fin_cases j <;> simp [f, Subtype.ext_iff, hvu, huv] at h ⊢
      · intro x
        have hx : (x : V) = u ∨ (x : V) = v := x.2
        rcases hx with hx | hx
        · refine ⟨1, ?_⟩; apply Subtype.ext; simpa [f] using hx.symm
        · refine ⟨0, ?_⟩; apply Subtype.ext; simpa [f] using hx.symm
    have h := Fintype.card_congr (Equiv.Set.sumCompl P)
    simp only [Fintype.card_sum] at h
    have hP : Fintype.card P = 2 := by
      simpa using (Fintype.card_congr (Equiv.ofBijective f hf)).symm
    change Fintype.card V = 2 + Fintype.card (Pᶜ : Set V)
    omega
  let e1 : {F : Finset V // v ∈ F} ≃ Finset (({v}ᶜ : Set V)) :=
    Equiv.ofBijective _ (petrial_leaf_flip_bijective v u huv)
  have hsum1 :
      (∑ F : {F : Finset V // v ∈ F},
        (X : Polynomial ℕ) ^ (Fintype.card V - (petrial_matrix T F.1).rank)) =
      petrial_nullity_poly (T.induce ({v}ᶜ : Set V)) := by
    unfold petrial_nullity_poly
    apply Fintype.sum_equiv e1
    intro F
    change (X : Polynomial ℕ) ^ (Fintype.card V - (petrial_matrix T F.1).rank) =
      (X : Polynomial ℕ) ^ (Fintype.card (({v}ᶜ : Set V)) -
        (petrial_matrix (T.induce ({v}ᶜ : Set V)) (petrial_leaf_flip v u F.1)).rank)
    rw [petrial_leaf_one_pivot T v u F.1 F.2 hu huniq, hc1]
    congr 1
    omega
  let e0 : {F : Finset V // v ∉ F} ≃ Bool × Finset (({u,v}ᶜ : Set V)) :=
    Equiv.ofBijective _ (petrial_leaf_restriction_bijective v u hvu)
  have hsum0 :
      (∑ F : {F : Finset V // v ∉ F},
        (X : Polynomial ℕ) ^ (Fintype.card V - (petrial_matrix T F.1).rank)) =
      2 * petrial_nullity_poly (T.induce (({u,v}ᶜ : Set V))) := by
    have hsum := Fintype.sum_equiv e0
      (fun F => (X : Polynomial ℕ) ^ (Fintype.card V - (petrial_matrix T F.1).rank))
      (fun p => (X : Polynomial ℕ) ^ (Fintype.card (({u,v}ᶜ : Set V)) -
        (petrial_matrix (T.induce (({u,v}ᶜ : Set V))) p.2).rank)) (by
          intro F
          change (X : Polynomial ℕ) ^ (Fintype.card V - (petrial_matrix T F.1).rank) =
            (X : Polynomial ℕ) ^ (Fintype.card (({u,v}ᶜ : Set V)) -
              (petrial_matrix (T.induce (({u,v}ᶜ : Set V))) (petrial_leaf_restriction v u F.1)).rank)
          rw [petrial_leaf_zero_pivot T v u F.1 F.2 hu huniq, hc2]
          congr 1
          omega)
    rw [hsum, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [petrial_nullity_poly, two_mul]
  change (∑ F : Finset V, (X : Polynomial ℕ) ^ (Fintype.card V - (petrial_matrix T F).rank)) =
    petrial_nullity_poly (T.induce ({v}ᶜ : Set V)) +
      2 * petrial_nullity_poly (T.induce (({u,v}ᶜ : Set V)))
  rw [← Fintype.sum_subtype_add_sum_subtype (fun F : Finset V => v ∈ F), hsum1, hsum0]
