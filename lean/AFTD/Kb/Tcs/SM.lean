import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub

/-!
# S_M

Topic: quantum   Node: 95ddfbc2a7ba

Provenance: formalization of a published result. Source: TCSlib, `S_M`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

For a submodule $S \le V$ and $M \subseteq \mathrm{Fin}\,n$, the submodule $S_M = S \cap V_M$.
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
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
/-- Intersection of S and V_M -/
noncomputable def S_M (S : Submodule (F p) (V n p)) (M : Finset (Fin n)) : Submodule (F p) (V n p) :=
  S ⊓ V_sub (p:=p) M
