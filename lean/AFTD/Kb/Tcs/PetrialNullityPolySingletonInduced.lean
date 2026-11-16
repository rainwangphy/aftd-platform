import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialNullityPoly
import AFTD.Kb.Tcs.PetrialMatrix

/-!
# petrial_nullity_poly_singleton_induced

Topic: combinatorics   Node: 85afefd11ee9

Provenance: helper lemma. Singleton base case for the OP-1239 leaf-deletion certificate.

The partial Petrial nullity generating polynomial of the graph induced on one vertex is one plus X.
-/

open Matrix Polynomial
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem petrial_nullity_poly_singleton_induced {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : petrial_nullity_poly (G.induce ({v} : Set V)) = 1 + Polynomial.X := by
  classical
  let S : Set V := {v}
  let a : S := ⟨v, rfl⟩
  letI : Unique S := {
    default := a
    uniq := by intro x; apply Subtype.ext; exact x.2
  }
  have hcard : Fintype.card S = 1 := Fintype.card_unique
  have hF : (Finset.univ : Finset (Finset S)) = {∅, Finset.univ} := by
    ext F
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases h : a ∈ F
    · right
      ext y
      have hy : y = a := Subsingleton.elim _ _
      subst y
      constructor
      · intro _; exact Finset.mem_univ _
      · intro _; exact h
    · left
      ext y
      have hy : y = a := Subsingleton.elim _ _
      subst y
      simp [h]
  have hne : (∅ : Finset S) ≠ Finset.univ := by
    intro h
    have hmem : a ∈ (∅ : Finset S) := h ▸ Finset.mem_univ a
    simpa using hmem
  have hM0 : petrial_matrix (G.induce S) (∅ : Finset S) = 0 := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [petrial_matrix]
  have hM1 : petrial_matrix (G.induce S) (Finset.univ : Finset S) = 1 := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [petrial_matrix, Subsingleton.elim i (default : S)]
  unfold petrial_nullity_poly
  change (∑ F : Finset S, (Polynomial.X : Polynomial ℕ) ^ (Fintype.card S - (petrial_matrix (G.induce S) F).rank)) = _
  rw [hF]
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton, hM0, hM1, Matrix.rank_zero, Matrix.rank_one, hcard]
  norm_num [add_comm]
