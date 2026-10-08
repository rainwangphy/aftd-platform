import AFTD.Prelude

/-!
# PauliNZ

Topic: quantum   Node: 3f800e44f95d

Provenance: formalization of a published result. Source: TCSlib, `PauliNZ`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 adapted, 1 added here; compiled here.

A 3-element type for non-identity single-qubit Pauli operators, used in counting arguments.
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
/-- A 3-element type for non-identity single-qubit Pauli operators, used in counting arguments. -/
inductive PauliNZ | X | Y | Z
deriving DecidableEq, Inhabited

instance PauliNZ.instFintype : Fintype PauliNZ :=
  ⟨{.X, .Y, .Z}, by intro x; cases x <;> decide⟩
