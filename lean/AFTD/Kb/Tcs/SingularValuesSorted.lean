import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValues

/-!
# singularValuesSorted

Topic: quantum   Node: 555a880f8c95

Provenance: formalization of a published result. Source: QuantumInfo, `singularValuesSorted`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The sorted singular values of a square complex matrix, in decreasing order, indexed by `Fin (Fintype.card d)`. We define them by sorting the multiset of singular values.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The sorted singular values of a square complex matrix, in decreasing order, indexed by `Fin (Fintype.card d)`. We define them by sorting the multiset of singular values. -/
noncomputable def singularValuesSorted (A : Matrix d d ℂ) :
    Fin (Fintype.card d) → ℝ :=
  fun i =>
    let vals : Multiset ℝ := Finset.univ.val.map (singularValues A)
    let sorted := vals.sort (· ≥ ·)
    sorted.get ⟨i.val, by rw [Multiset.length_sort]; show i.val < (Multiset.map (singularValues A) univ.val).card; rw [Multiset.card_map]; simp [Finset.card_univ]⟩
