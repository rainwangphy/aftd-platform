import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.ExtendFromC
import AFTD.Kb.Tcs.ExtendFromCRestrictToC
import AFTD.Kb.Tcs.RestrictToC
import AFTD.Kb.Tcs.RestrictToCExtendFromC

/-!
# V_sub_iso

Topic: quantum   Node: 3f81b9ad8eea

Provenance: formalization of a published result. Source: TCSlib, `V_sub_iso`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

V_sub_iso
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
noncomputable def V_sub_iso (C : Finset (Fin n)) :
    V_sub (p:=p) C ≃ₗ[F p] (C → F p) × (C → F p) where
  toFun := restrictToC (p:=p) C
  invFun := extendFromC (p:=p) C
  left_inv := extendFromC_restrictToC (p:=p) C
  right_inv := restrictToC_extendFromC (p:=p) C
  map_add' := (restrictToC (p:=p) C).map_add'
  map_smul' := (restrictToC (p:=p) C).map_smul'


/-
Dimension of a support subspace V_C is 2|C|.
-/
