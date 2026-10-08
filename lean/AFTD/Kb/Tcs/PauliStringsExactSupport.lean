import AFTD.Prelude
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.Support
import AFTD.Kb.Tcs.InstFintypePauliString

/-!
# pauliStringsExactSupport

Topic: quantum   Node: 524f0384d447

Provenance: formalization of a published result. Source: TCSlib, `pauliStringsExactSupport`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

The finset of all Pauli strings on $n$ qubits whose support equals exactly the given
finset $S$.
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
/-- The finset of Pauli strings with support exactly equal to `S`. -/
noncomputable def pauliStringsExactSupport {n : ℕ} (S : Finset (Fin n)) : Finset (PauliString n) :=
  Finset.filter (fun p => support p = S) Finset.univ
