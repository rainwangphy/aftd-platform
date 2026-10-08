import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.SymB

/-!
# sym_orth

Topic: quantum   Node: 1ed33b581e77

Provenance: formalization of a published result. Source: TCSlib, `sym_orth`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

For a submodule $S \le V$,
$S^{\perp_\omega} = \{v \in V \mid \forall s \in S,\; \omega(v,s) = 0\}$.
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
/-- Orthogonal complement with respect to the symplectic bilinear form. -/
noncomputable abbrev sym_orth (S : Submodule (F p) (V n p)) : Submodule (F p) (V n p) :=
  (symB (n:=n) (p:=p)).orthogonal S
