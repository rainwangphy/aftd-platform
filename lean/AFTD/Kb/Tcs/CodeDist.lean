import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.SymOrth
import AFTD.Kb.Tcs.Wt

/-!
# code_dist

Topic: quantum   Node: d2ffc86c65b8

Provenance: formalization of a published result. Source: TCSlib, `code_dist`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

$d(S) = \min\{\mathrm{wt}(v) \mid v \in S^{\perp_\omega} \setminus S,\; \mathrm{wt}(v) \neq 0\}$
(or $0$ if no such $v$ exists).
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
/-- The distance of the stabilizer code defined by S -/
noncomputable def code_dist (S : Submodule (F p) (V n p)) : ℕ :=
  sInf {d | ∃ v ∈ sym_orth S, v ∉ S ∧ wt v = d}

/-
Definition of correctable erasure.
-/
