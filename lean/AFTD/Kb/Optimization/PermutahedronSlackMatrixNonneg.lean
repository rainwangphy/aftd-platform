import AFTD.Prelude
import AFTD.Kb.Optimization.PermutahedronSlackMatrix

/-!
# permutahedron_slack_matrix_nonneg

Topic: integer_programming   Node: 09ecc9a510e7

Provenance: formalization of a published result. Source: arXiv:2610.04498 Sec. 4.2

For every natural number n, nonempty proper subset S of Fin n, and permutation σ of Fin n, the entry of the permutahedron slack matrix at (S, σ) is nonnegative.
-/

lemma permutahedron_slack_matrix_nonneg_finset_card_succ_choose_two_le_sum_add_card
    (T : Finset ℕ) :
    (T.card + 1).choose 2 ≤ (∑ x ∈ T, x) + T.card := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a T hlt ih =>
      have haT : a ∉ T := by
        intro ha
        exact (Nat.lt_irrefl a) (hlt a ha)
      have hcard : T.card ≤ a := by
        calc T.card ≤ (Finset.range a).card := by
              apply Finset.card_le_card
              intro x hx
              exact Finset.mem_range.mpr (hlt x hx)
          _ = a := Finset.card_range a
      rw [Finset.card_insert_of_notMem haT, Finset.sum_insert haT]
      have hchoose : (T.card + 1 + 1).choose 2 = (T.card + 1).choose 2 + (T.card + 1) := by
        rw [show (T.card + 1 + 1).choose 2 = (T.card + 1) + (T.card + 1).choose 2 from by
          simpa using Nat.choose_succ_succ (T.card + 1) 1]
        omega
      rw [hchoose]
      omega

/-- Every entry of the permutahedron slack matrix is nonnegative. -/
theorem permutahedron_slack_matrix_nonneg (n : ℕ) (S : {S : Finset (Fin n) // S.Nonempty ∧ S ≠ Finset.univ}) (σ : Equiv.Perm (Fin n)) : 0 ≤ permutahedron_slack_matrix n S σ := by
  let T : Finset ℕ := S.val.image (fun i : Fin n => (σ i).val)
  have hinj : Set.InjOn (fun i : Fin n => (σ i).val) ↑S.val := by
    intro i hi j hj hij
    exact σ.injective (Fin.ext hij)
  have hcardT : T.card = S.val.card := by
    simpa [T] using Finset.card_image_of_injOn hinj
  have hsumT : ∑ x ∈ T, x = ∑ i ∈ S.val, (σ i).val := by
    simpa [T] using
      (Finset.sum_image (s := S.val) (g := fun i : Fin n => (σ i).val)
        (f := fun x : ℕ => x) hinj)
  have hmain : ((S.val.card + 1).choose 2 : ℝ) ≤
      (∑ i ∈ S.val, ((σ i).val : ℝ)) + (S.val.card : ℝ) := by
    have h := permutahedron_slack_matrix_nonneg_finset_card_succ_choose_two_le_sum_add_card T
    rw [hcardT, hsumT] at h
    exact_mod_cast h
  have hsum1 : (∑ i ∈ S.val, ((σ i).val + 1 : ℝ)) =
      (∑ i ∈ S.val, ((σ i).val : ℝ)) + (S.val.card : ℝ) := by
    rw [Finset.sum_add_distrib]
    simp
  unfold permutahedron_slack_matrix
  rw [hsum1]
  linarith
