import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBasis

/-!
# PauliString

Topic: quantum   Node: b9d9be37a56d

Provenance: formalization of a published result. Source: TCSlib, `PauliString`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

A \emph{Pauli string} of length $n$ is a function $p : \mathrm{Fin}\,n \to \mathrm{PauliBasis}$.
-/

set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open scoped Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Complex Matrix in
/-- An n-qubit Pauli string: a function assigning a Pauli basis element to each of the n qubits. -/
noncomputable def PauliString (n : ℕ) := Fin n → PauliBasis
