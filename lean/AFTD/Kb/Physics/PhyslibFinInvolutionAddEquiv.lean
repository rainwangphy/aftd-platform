import AFTD.Prelude

/-!
# Physlib.Fin.involutionAddEquiv

Topic: classical_mechanics   Node: cf8128ac863e

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionAddEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given an involution of `Fin n`, the optional choice of an element in `Fin n` which maps to itself is equivalent to the optional choice of an element in `Fin (Finset.univ.filter fun i => f.1 i = i).card`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
/-- Given an involution of `Fin n`, the optional choice of an element in `Fin n` which maps to itself is equivalent to the optional choice of an element in `Fin (Finset.univ.filter fun i => f.1 i = i).card`. -/
def Physlib.Fin.involutionAddEquiv {n : ℕ} (f : {f : Fin n → Fin n // Function.Involutive f}) :
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)} ≃
    Option (Fin (Finset.univ.filter fun i => f.1 i = i).card) := by
  let e1 : {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)}
        ≃ Option {i : Fin n // f.1 i = i} :=
    { toFun := fun i => match i with
        | ⟨some i, h⟩ => some ⟨i, by simpa using h⟩
        | ⟨none, h⟩ => none
      invFun := fun i => match i with
        | some ⟨i, h⟩ => ⟨some i, by simpa using h⟩
        | none => ⟨none, by simp⟩
      left_inv := by
        rintro ⟨_ | i, h⟩ <;> rfl
      right_inv := by
        rintro (_ | ⟨i, h⟩) <;> rfl }
  let s : Finset (Fin n) := Finset.univ.filter fun i => f.1 i = i
  let e2' : { i : Fin n // f.1 i = i} ≃ {i // i ∈ s} := by
    apply Equiv.subtypeEquivProp
    simp [s]
  let e2 : {i // i ∈ s} ≃ Fin (Finset.card s) := by
    refine (Finset.orderIsoOfFin _ ?_).symm.toEquiv
    simp [s]
  refine e1.trans (Equiv.optionCongr (e2'.trans (e2)))
