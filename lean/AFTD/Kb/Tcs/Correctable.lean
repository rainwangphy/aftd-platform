import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.SymOrth

/-!
# correctable

Topic: quantum   Node: cff0faf4beee

Provenance: formalization of a published result. Source: TCSlib, `correctable`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

An erasure set $E \subseteq \mathrm{Fin}\,n$ is \emph{correctable} for $S$ if
every $v \in V_E \cap S^{\perp_\omega}$ is already in $S$.
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
/-- Correctable erasure (commutant form) -/
noncomputable def correctable (S : Submodule (F p) (V n p)) (E : Finset (Fin n)) : Prop :=
  sym_orth S ⊓ V_sub (p:=p) E ≤ S

/-
Distance implies erasure correctability.
-/
