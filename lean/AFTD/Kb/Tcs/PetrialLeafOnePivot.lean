import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialLeafFlip
import AFTD.Kb.Tcs.PetrialMatrix
import AFTD.Kb.Tcs.PetrialRankSchurInvertible

/-!
# petrial_leaf_one_pivot

Topic: combinatorics   Node: 68556289b087

Provenance: helper lemma. One-vertex pivot case in the leaf-elimination recurrence for OP-1239.

If v is a leaf with unique neighbor u and the diagonal perturbation includes v, the perturbed matrix rank is one plus the rank on the graph with v removed, where the perturbation is restricted and membership of u is toggled.
-/

theorem petrial_leaf_one_pivot {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) (F : Finset V) (hF : v ∈ F) (hu : G.Adj v u) (huniq : ∀ w, G.Adj v w → w = u) : (petrial_matrix G F).rank = 1 + (petrial_matrix (G.induce ({v}ᶜ : Set V)) (petrial_leaf_flip v u F)).rank := by
  classical
  let P : Set V := {v}
  let e := Equiv.Set.sumCompl P
  let M := (petrial_matrix G F).submatrix e e
  have hn : u ≠ v := (G.ne_of_adj hu).symm
  letI : Unique P := {
    default := ⟨v, by simp [P]⟩
    uniq := by intro x; apply Subtype.ext; exact x.2
  }
  have hA : M.toBlocks₁₁ = 1 := by
    ext i j
    have hi : (i : V) = v := i.2
    have hj : (j : V) = v := j.2
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [Matrix.one_apply_eq]
    change (petrial_matrix G F) i.1 i.1 = 1
    rw [hi]
    simp [petrial_matrix, hF]
  letI : Invertible (1 : Matrix P P (ZMod 2)) := invertibleOne
  have hschur := petrial_rank_schur_invertible (1 : Matrix P P (ZMod 2)) M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂
  simp only [invOf_one, Matrix.mul_one, Fintype.card_unique] at hschur
  rw [← hA, Matrix.fromBlocks_toBlocks] at hschur
  have hmat : M.toBlocks₂₂ - M.toBlocks₂₁ * M.toBlocks₁₂ =
      petrial_matrix (G.induce ({v}ᶜ : Set V)) (petrial_leaf_flip v u F) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_unique]
    change (petrial_matrix G F) i.1 j.1 - (petrial_matrix G F) i.1 v *
      (petrial_matrix G F) v j.1 = _
    simp only [petrial_matrix, Matrix.add_apply, SimpleGraph.adjMatrix_apply,
      Matrix.diagonal_apply, Finset.mem_filter, Finset.mem_univ, true_and,
      petrial_leaf_flip, SimpleGraph.induce_adj]
    have hiv : (i : V) ≠ v := i.2
    have hjv : (j : V) ≠ v := j.2
    have ha : G.Adj (i : V) v ↔ (i : V) = u := by
      constructor
      · intro h; exact huniq _ h.symm
      · intro h; rw [h]; exact hu.symm
    have hb : G.Adj v (j : V) ↔ (j : V) = u := by
      constructor
      · exact huniq _
      · intro h; rw [h]; exact hu
    simp only [hiv, Ne.symm hjv, if_false, ha, hb, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hij : i = j
    · subst j
      by_cases hiu : (i : V) = u <;> by_cases hf : (i : V) ∈ F <;>
        simp_all <;> try ring_nf
    · have hijv : (i : V) ≠ (j : V) := fun h => hij (Subtype.ext h)
      by_cases hiu : (i : V) = u
      · have hju : (j : V) ≠ u := fun h => hijv (hiu.trans h.symm)
        simp [hij, hijv, hiu, hju, Ne.symm hju]
      · simp [hij, hijv, hiu]
  rw [hmat] at hschur
  simpa [M] using hschur
