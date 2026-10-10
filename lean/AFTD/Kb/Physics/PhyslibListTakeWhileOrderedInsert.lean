import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedSetOne

/-!
# Physlib.List.takeWhile_orderedInsert

Topic: classical_mechanics   Node: eae3e23fa44c

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.takeWhile_orderedInsert`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertionSort.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.takeWhile_orderedInsert
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open _root_.Physlib.Fin in
variable {n : Nat} in
lemma Physlib.List.takeWhile_orderedInsert {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r]
    (a b : α) (hr : ¬ r a b) : (l : List α) →
    (List.takeWhile (fun c => !decide (r a c)) (List.orderedInsert r b l)).length =
    (List.takeWhile (fun c => !decide (r a c)) l).length + 1
  | [] => by
    simp [hr]
  | c :: l => by
    simp only [List.orderedInsert]
    by_cases h : r b c
    · simp [h, hr]
    · simp only [h, ↓reduceIte]
      have hl : ¬ r a c :=
        fun hn => h (IsTrans.trans _ _ _ ((Std.Total.total a b).resolve_left hr) hn)
      simp only [hl, decide_false, Bool.not_false, List.takeWhile_cons_of_pos, List.length_cons,
        add_left_inj]
      exact takeWhile_orderedInsert r a b hr l
