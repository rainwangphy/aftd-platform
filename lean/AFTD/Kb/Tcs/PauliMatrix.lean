import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBasisToMatrix
import AFTD.Kb.Tcs.PauliString

/-!
# pauliMatrix

Topic: quantum   Node: a877b2358826

Provenance: formalization of a published result. Source: TCSlib, `pauliMatrix`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

For a Pauli string $p$ on $n$ qubits, the $2^n\times 2^n$ matrix obtained as the
tensor product of the single-qubit Pauli matrices $\sigma_{p(i)}$ over all coordinates~$i$.
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
/-- The 2^n × 2^n matrix for an n-qubit Pauli string, given as a tensor product of single-qubit Pauli matrices. -/
noncomputable def pauliMatrix {n : ℕ} (p : PauliString n) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun i j => ∏ k, (p k).toMatrix (i k) (j k)
