import AFTD.Prelude
import AFTD.Kb.Tcs.F

/-!
# V

Topic: quantum   Node: a93a9d0f115d

Provenance: formalization of a published result. Source: TCSlib, `V`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

The ambient space $V = \mathbb{F}_p^n \times \mathbb{F}_p^n$ of pairs of coordinate vectors.
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
/-- The symplectic vector space V := F^n × F^n -/
noncomputable abbrev V (n p : ℕ) [Fact p.Prime] := (Fin n → F p) × (Fin n → F p)
