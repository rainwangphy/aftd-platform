import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialLeafRestriction
import AFTD.Kb.Tcs.PetrialMatrix
import AFTD.Kb.Tcs.PetrialRankSchurInvertible

/-!
# petrial_leaf_zero_pivot

Topic: combinatorics   Node: 77ff29bf5599

Provenance: helper lemma. Helper for the partial Petrial leaf recurrence and OP-1239.

For a graph with a leaf v and unique neighbor u, if v is absent from the perturbation then its matrix rank is two plus the rank on the graph obtained by deleting u and v, with the perturbation restricted.
-/

theorem petrial_leaf_zero_pivot {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (F : Finset V)
    (hF : v ∉ F) (hu : G.Adj v u) (huniq : ∀ w, G.Adj v w → w = u) :
    (petrial_matrix G F).rank =
      2 + (petrial_matrix (G.induce ({u, v}ᶜ : Set V)) (petrial_leaf_restriction v u F)).rank := by
  classical
  have hvu : v ≠ u := G.ne_of_adj hu
  let P : Set V := {u, v}
  let f : Fin 2 → P := fun i => if i = 0 then ⟨v, by simp [P]⟩ else ⟨u, by simp [P]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff]
    · intro x
      have hx : (x : V) = u ∨ (x : V) = v := x.2
      rcases hx with hx | hx
      · refine ⟨1, ?_⟩; apply Subtype.ext; simpa [f] using hx.symm
      · refine ⟨0, ?_⟩; apply Subtype.ext; simpa [f] using hx.symm
  let pe : Fin 2 ≃ P := Equiv.ofBijective f hf
  let e : Fin 2 ⊕ (Pᶜ : Set V) ≃ V := (Equiv.sumCongr pe (Equiv.refl _)).trans (Equiv.Set.sumCompl P)
  let M := (petrial_matrix G F).submatrix e e
  let d : ZMod 2 := if u ∈ F then 1 else 0
  let A : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, d]
  have hA : M.toBlocks₁₁ = A := by
    ext i j
    change (petrial_matrix G F) (pe i).1 (pe j).1 = A i j
    fin_cases i <;> fin_cases j <;>
      simp [pe, f, A, d, petrial_matrix, Matrix.diagonal_apply, hF, hu, hu.symm, hvu, Ne.symm hvu]
  have hdet : IsUnit A.det := by
    have hd : A.det = 1 := by
      simp [A, Matrix.det_fin_two]
    rw [hd]
    exact isUnit_one
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hdet
  have hinv : (⅟A) 1 1 = 0 := by
    have h := congrArg (fun (X : Matrix (Fin 2) (Fin 2) (ZMod 2)) => X 0 1) (mul_invOf_self A)
    simpa [Matrix.mul_apply, Fin.sum_univ_two, A] using h
  have hcol (i : (Pᶜ : Set V)) : M.toBlocks₂₁ i 0 = 0 := by
    change (petrial_matrix G F) i.1 v = 0
    have hiu : (i : V) ≠ u := by
      intro h
      have hi : (i : V) ∉ P := i.2
      apply hi
      simp [P, h]
    have hiv : (i : V) ≠ v := by
      intro h
      have hi : (i : V) ∉ P := i.2
      apply hi
      simp [P, h]
    have hadj : ¬ G.Adj (i : V) v := fun h => hiu (huniq _ h.symm)
    simp [petrial_matrix, Matrix.diagonal_apply, hadj, hiv]
  have hrow (j : (Pᶜ : Set V)) : M.toBlocks₁₂ 0 j = 0 := by
    change (petrial_matrix G F) v j.1 = 0
    have hju : (j : V) ≠ u := by
      intro h
      have hj : (j : V) ∉ P := j.2
      apply hj
      simp [P, h]
    have hjv : (j : V) ≠ v := by
      intro h
      have hj : (j : V) ∉ P := j.2
      apply hj
      simp [P, h]
    have hadj : ¬ G.Adj v (j : V) := fun h => hju (huniq _ h)
    simp [petrial_matrix, Matrix.diagonal_apply, hadj, Ne.symm hjv]
  have hprod : M.toBlocks₂₁ * ⅟A * M.toBlocks₁₂ = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hcol, hrow, hinv, zero_mul,
      mul_zero, zero_add, add_zero, Matrix.zero_apply]
  have hD : M.toBlocks₂₂ = petrial_matrix (G.induce ({u, v}ᶜ : Set V))
      (petrial_leaf_restriction v u F) := by
    ext i j
    change (petrial_matrix G F) i.1 j.1 = _
    simp [petrial_matrix, petrial_leaf_restriction, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply, Subtype.ext_iff]
  have hschur := petrial_rank_schur_invertible A M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
  have hrank : M.rank = (Matrix.fromBlocks A M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂).rank := by
    conv_lhs => rw [← M.fromBlocks_toBlocks]
    rw [hA]
  rw [← Matrix.rank_submatrix (petrial_matrix G F) e e, ← show M.rank = _ from rfl,
    hrank, hschur]
  rw [hprod, sub_zero, hD]
  simp
