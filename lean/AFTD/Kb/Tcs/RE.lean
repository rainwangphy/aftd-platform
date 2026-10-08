import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub

/-!
# r_E

Topic: quantum   Node: 95bfa0490494

Provenance: formalization of a published result. Source: TCSlib, `r_E`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

The linear map $r_E : V \to V_E$ that zeroes out the coordinates of a vector outside $E$,
keeping those in $E$ unchanged.
-/

open scoped BigOperators in
set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
set_option linter.unnecessarySimpa false in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
/-- Restriction map r_E : V -> V_E -/
noncomputable def r_E (E : Finset (Fin n)) : V n p →ₗ[F p] V_sub (p:=p) E where
  toFun v := ⟨(fun i => if i ∈ E then v.1 i else 0, fun i => if i ∈ E then v.2 i else 0), by
    exact fun i hi => by simp_all only [↓reduceIte, and_self];⟩
  map_add' := by
    intro x y
    simp_all only [Prod.fst_add, Pi.add_apply, Prod.snd_add]
    obtain ⟨fst, snd⟩ := x
    obtain ⟨fst_1, snd_1⟩ := y
    simp_all only [AddMemClass.mk_add_mk, Prod.mk_add_mk, Subtype.mk.injEq, Prod.mk.injEq]
    apply And.intro
    · ext x : 1
      simp_all only [Pi.add_apply]
      split
      next h => simp_all only
      next h => simp_all only [add_zero]
    · ext x : 1
      simp_all only [Pi.add_apply]
      split
      next h => simp_all only
      next h => simp_all only [add_zero]
  map_smul' := by
    intro m x
    simp_all only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Prod.smul_snd, RingHom.id_apply]
    obtain ⟨fst, snd⟩ := x
    simp_all only [SetLike.mk_smul_mk, Prod.smul_mk, Subtype.mk.injEq, Prod.mk.injEq]
    apply And.intro
    · ext x : 1
      simp_all only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero]
    · ext x : 1
      simp_all only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero]

/-
Definitions of symplectic orthogonal complement, isotropic subspace, and code distance.
-/
