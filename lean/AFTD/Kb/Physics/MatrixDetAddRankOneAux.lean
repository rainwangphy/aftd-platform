import AFTD.Prelude

/-!
# Matrix.det_add_rankOne_aux

Topic: classical_mechanics   Node: 61291277f8ba

Provenance: formalization of a published result. Source: Physlib, `Matrix.det_add_rankOne_aux`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Contraction.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expanding the determinant of a rank-one row update over a finite set of rows. For `i ∈ s` the row `A i` is replaced by `A i + w i • b`; the other rows are untouched.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
/-- Expanding the determinant of a rank-one row update over a finite set of rows. For `i ∈ s` the row `A i` is replaced by `A i + w i • b`; the other rows are untouched. -/
lemma Matrix.det_add_rankOne_aux {ι : Type*} [DecidableEq ι] [Fintype ι] {R : Type*}
    [CommRing R] (A : Matrix ι ι R) (w b : ι → R) (s : Finset ι) :
    (A + Matrix.of fun i j => (if i ∈ s then w i else 0) * b j).det
      = A.det + ∑ i ∈ s, w i * (A.updateRow i b).det := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h0 : (Matrix.of fun (i : ι) (j : ι) =>
        (if i ∈ (∅ : Finset ι) then w i else 0) * b j) = 0 := by
      ext i j; simp
    rw [h0, add_zero, Finset.sum_empty, add_zero]
  | @insert i₀ s hi₀ ih =>
    -- The new matrix differs from the `s`-matrix only in row `i₀`, by `+ w i₀ • b`.
    set Ms : Matrix ι ι R := A + Matrix.of fun i j => (if i ∈ s then w i else 0) * b j with hMs
    have hrow : Ms i₀ = A i₀ := by
      funext j; simp [hMs, hi₀]
    have key : (A + Matrix.of fun i j => (if i ∈ insert i₀ s then w i else 0) * b j)
        = Ms.updateRow i₀ (A i₀ + w i₀ • b) := by
      ext i j
      by_cases hi : i = i₀
      · subst hi
        simp [Matrix.updateRow_self, hi₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      · rw [Matrix.updateRow_ne hi]
        simp [hMs, Finset.mem_insert, hi]
    rw [key, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
    -- The `A i₀` part rebuilds `Ms`; the `b` part is `det (updateRow A i₀ b)` after column ops.
    have h1 : (Ms.updateRow i₀ (A i₀)).det = Ms.det := by
      rw [← hrow, Matrix.updateRow_eq_self]
    have h2 : (Ms.updateRow i₀ b).det = (A.updateRow i₀ b).det := by
      refine Matrix.det_eq_of_forall_row_eq_smul_add_const
        (fun i => if i ∈ s then w i else 0) i₀ (by simp [hi₀]) ?_
      intro i j
      by_cases hi : i = i₀
      · subst hi
        simp [Matrix.updateRow_self, hi₀]
      · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi, Matrix.updateRow_self, hMs]
        simp [Matrix.add_apply]
    rw [h1, h2, ih, Finset.sum_insert hi₀]
    ring
