import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V

/-!
# sym_form

Topic: quantum   Node: 6492b5e0b563

Provenance: formalization of a published result. Source: TCSlib, `sym_form`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

For $u = (x,z), v = (x',z') \in V = \mathbb{F}_p^n \times \mathbb{F}_p^n$,
\[
\omega(u,v) \;=\; \sum_{i=0}^{n-1}(x_i z'_i - z_i x'_i).
\]
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
/-- Standard symplectic form on V: `sym_form (u, v) = ∑ i, u₁ᵢ v₂ᵢ - u₂ᵢ v₁ᵢ`. -/
noncomputable def sym_form (u v : V n p) : F p :=
  Finset.univ.sum (fun i : Fin n => (u.1 i * v.2 i - u.2 i * v.1 i))
