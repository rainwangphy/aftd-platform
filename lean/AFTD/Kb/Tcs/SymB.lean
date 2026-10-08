import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.SymForm
import AFTD.Kb.Tcs.SymFormAddLeft
import AFTD.Kb.Tcs.SymFormAddRight
import AFTD.Kb.Tcs.SymFormSmulLeft
import AFTD.Kb.Tcs.SymFormSmulRight

/-!
# symB

Topic: quantum   Node: f75c0e0e422e

Provenance: formalization of a published result. Source: TCSlib, `symB`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

$\omega$ packaged as a \texttt{LinearMap.BilinForm}.
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
/-- The standard symplectic form `sym_form` packaged as a `LinearMap.BilinForm`. -/
noncomputable def symB : LinearMap.BilinForm (F p) (V n p) :=
  LinearMap.mk₂ (F p) (fun x y => sym_form (n:=n) (p:=p) x y)
    (by intro x y z; simpa using sym_form_add_left (n:=n) (p:=p) x y z)
    (by intro c x y; simpa using sym_form_smul_left (n:=n) (p:=p) c x y)
    (by intro x y z; simpa using sym_form_add_right (n:=n) (p:=p) x y z)
    (by intro c x y; simpa using sym_form_smul_right (n:=n) (p:=p) c x y)
