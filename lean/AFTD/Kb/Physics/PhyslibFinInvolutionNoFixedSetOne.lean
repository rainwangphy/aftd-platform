import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedZeroSetEquivSetOne
import AFTD.Kb.Physics.FinSuccSuccAboveInjective

/-!
# Physlib.Fin.involutionNoFixedSetOne

Topic: classical_mechanics   Node: 0c5c704b0b68

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixedSetOne`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fixed point involutions of `Fin n.succ.succ` fixing `f 0 = 1` are equivalent to fixed point involutions of `Fin n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
/-- Fixed point involutions of `Fin n.succ.succ` fixing `f 0 = 1` are equivalent to fixed point involutions of `Fin n`. -/
def Physlib.Fin.involutionNoFixedSetOne {n : ℕ} :
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧
    (∀ i, f i ≠ i) ∧ f 0 = 1} ≃ {f : Fin n → Fin n // Function.Involutive f ∧
    (∀ i, f i ≠ i)} where
  toFun f := by
    have f_succ_succ_ne_zero_one (i : Fin n) : f.1 i.succ.succ ≠ 0 ∧ f.1 i.succ.succ ≠ 1 := by
      have hf1 : f.1 1 = 0 := by
        simp only [← f.2.2.2]
        rw [f.2.1]
      refine ⟨fun hn => ?_, fun hn => ?_⟩
      · simpa [Fin.ext_iff] using f.2.1.injective (hn.trans hf1.symm)
      · simpa [Fin.ext_iff] using f.2.1.injective (hn.trans f.2.2.2.symm)
    let f' := f.1 ∘ Fin.succ ∘ Fin.succ
    have hf' (i : Fin n) : f' i ≠ 0 := (f_succ_succ_ne_zero_one i).1
    let f'' := fun i => (f' i).pred (hf' i)
    have hf'' (i : Fin n) : f'' i ≠ 0 := by
      rw [ne_eq, Fin.pred_eq_iff_eq_succ, Fin.succ_zero_eq_one]
      exact (f_succ_succ_ne_zero_one i).2
    let f''' := fun i => (f'' i).pred (hf'' i)
    refine ⟨f''', ?_, ?_⟩
    · intro i
      simp only [succ_eq_add_one, ne_eq, Function.comp_apply, Fin.succ_pred, f''', f'', f']
      simp [f.2.1 i.succ.succ]
    · intro i
      simp only [succ_eq_add_one, ne_eq, Function.comp_apply, f''', f'', f']
      rw [Fin.pred_eq_iff_eq_succ, Fin.pred_eq_iff_eq_succ]
      exact f.2.2.1 i.succ.succ
  invFun f := by
    let f' := fun (i : Fin n.succ.succ)=>
      match i with
      | ⟨0, h⟩ => 1
      | ⟨1, h⟩ => 0
      | ⟨(Nat.succ (Nat.succ n)), h⟩ => (f.1 ⟨n, by omega⟩).succ.succ
    refine ⟨f', ?_, ?_, ?_⟩
    · intro i
      match i with
      | ⟨0, h⟩ => rfl
      | ⟨1, h⟩ => rfl
      | ⟨(Nat.succ (Nat.succ m)), h⟩ =>
        simp only [succ_eq_add_one, ne_eq, f']
        split
        · rename_i h
          simp [Fin.ext_iff] at h
        · rename_i h
          simp [Fin.ext_iff] at h
        · rename_i h
          rename_i x r
          simp_all only [succ_eq_add_one, Fin.ext_iff, Fin.val_succ, add_left_inj]
          have ht : f.1 ⟨m, by omega⟩ = ⟨x, by omega⟩ := Fin.ext h
          rw [← ht, f.2.1]
    · intro i
      match i with
      | ⟨0, h⟩ =>
        simp only [succ_eq_add_one, ne_eq, Fin.zero_eta, f']
        split <;> try simp_all
      | ⟨1, h⟩ =>
        simp only [succ_eq_add_one, ne_eq, Fin.mk_one, f']
        split <;> try simp_all
      | ⟨(Nat.succ (Nat.succ m)), h⟩ =>
        simp only [succ_eq_add_one, ne_eq, Fin.ext_iff, Fin.val_succ, add_left_inj, f']
        have hf := f.2.2 ⟨m, Nat.add_lt_add_iff_right.mp h⟩
        simp only [ne_eq, Fin.ext_iff] at hf
        omega
    · simp only [succ_eq_add_one, ne_eq, f']
      split <;> try simp_all
  left_inv f := by
    have hf1 : f.1 1 = 0 := by
      simp only [succ_eq_add_one, ne_eq, ← f.2.2.2]
      rw [f.2.1]
    simp only [succ_eq_add_one, ne_eq, Function.comp_apply, Fin.succ_mk, Fin.succ_pred]
    ext i
    simp only
    split
    · simp [succ_eq_add_one, Fin.zero_eta, f.2.2.2]
    · exact congrArg Fin.val hf1.symm
    · exact rfl
  right_inv f := by
    simp only [ne_eq, succ_eq_add_one, Function.comp_apply]
    ext i
    simp only [Fin.val_pred]
    split
    · rename_i h
      simp [Fin.ext_iff] at h
    · rename_i h
      simp [Fin.ext_iff] at h
    · simp only [Fin.val_succ, add_tsub_cancel_right]
      congr
      apply congrArg
      simp_all [Fin.ext_iff]
