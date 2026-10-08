import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.SM
import AFTD.Kb.Tcs.SPerpM
import AFTD.Kb.Tcs.V

/-!
# g

Topic: quantum   Node: df239c4465cd

Provenance: formalization of a published result. Source: TCSlib, `g`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

$g(S,M) = \dim_{\mathbb{F}_p}(S^{\perp}_M) - \dim_{\mathbb{F}_p}(S_M)$.
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
/-- Supportable logical operators count g(M) -/
noncomputable def g (S : Submodule (F p) (V n p)) (M : Finset (Fin n)) : ℕ :=
  Module.finrank (F p) (S_perp_M S M) - Module.finrank (F p) (S_M S M)

/-
Checking FiniteDimensional instances.
-/
