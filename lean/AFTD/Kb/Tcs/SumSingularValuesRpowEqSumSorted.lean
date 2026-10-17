import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValues
import AFTD.Kb.Tcs.SingularValuesSorted

/-!
# sum_singularValues_rpow_eq_sum_sorted

Topic: quantum   Node: 8844d901f54f

Provenance: formalization of a published result. Source: QuantumInfo, `sum_singularValues_rpow_eq_sum_sorted`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The sum `∑ singularValues A i ^ p` equals the sum over sorted singular values.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The sum `∑ singularValues A i ^ p` equals the sum over sorted singular values. -/
lemma sum_singularValues_rpow_eq_sum_sorted (A : Matrix d d ℂ) (p : ℝ) :
    ∑ i : d, singularValues A i ^ p =
    ∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p := by
  have h_perm : Multiset.map (fun i => singularValues A i) Finset.univ.val = Multiset.map (fun i => singularValuesSorted A i) Finset.univ.val := by
    have h_multiset : Multiset.map (fun i => singularValues A i) Finset.univ.val = Multiset.sort (Multiset.map (fun i => singularValues A i) Finset.univ.val) (· ≥ ·) := by
      aesop
    convert h_multiset using 1
    refine' congr_arg _ (List.ext_get _ _) <;> simp [singularValuesSorted]
  have h_sum_eq : Multiset.sum (Multiset.map (fun x => x ^ p) (Multiset.map (fun i => singularValues A i) Finset.univ.val)) = Multiset.sum (Multiset.map (fun x => x ^ p) (Multiset.map (fun i => singularValuesSorted A i) Finset.univ.val)) := by
    rw [h_perm]
  convert h_sum_eq using 1
  · erw [Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  · simp [Finset.sum]
    rfl
