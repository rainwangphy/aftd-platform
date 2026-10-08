import AFTD.Prelude

/-!
# F

Topic: quantum   Node: eefb361e75c4

Provenance: formalization of a published result. Source: TCSlib, `F`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

The prime field $\mathrm{GF}(p)$, realized as $\mathbb{Z}/p\mathbb{Z}$ via \texttt{ZMod}.
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
/-- The prime field `GF(p)`, realized as `ZMod p`. -/
noncomputable abbrev F (p : ℕ) [Fact p.Prime] := ZMod p
