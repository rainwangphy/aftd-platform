import AFTD.Prelude
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliMatrix

/-!
# pauliOp

Topic: quantum   Node: bb28a47b98eb

Provenance: formalization of a published result. Source: TCSlib, `pauliOp`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

For $p \in \mathrm{PauliString}\,n$, the associated Pauli operator
$\hat{p} : \mathcal{H}_n \to \mathcal{H}_n$.
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
/-- The linear operator on `Hn n` given by acting with the Pauli string `p`. -/
noncomputable def pauliOp {n : ℕ} (p : PauliString n) : Hn n →ₗ[ℂ] Hn n :=
  Matrix.toEuclideanLin (pauliMatrix p)
