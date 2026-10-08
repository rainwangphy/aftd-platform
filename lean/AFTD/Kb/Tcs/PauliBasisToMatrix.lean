import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBasis
import AFTD.Kb.Tcs.SigmaI
import AFTD.Kb.Tcs.SigmaX
import AFTD.Kb.Tcs.SigmaY
import AFTD.Kb.Tcs.SigmaZ

/-!
# PauliBasis.toMatrix

Topic: quantum   Node: 5ef1f4875810

Provenance: formalization of a published result. Source: TCSlib, `PauliBasis.toMatrix`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

Maps each Pauli basis element $\{I,X,Y,Z\}$ to its corresponding $2\times 2$ matrix
$\{\sigma_I,\sigma_X,\sigma_Y,\sigma_Z\}$.
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
/-- Maps each Pauli basis element to its corresponding 2×2 matrix. -/
noncomputable def PauliBasis.toMatrix : PauliBasis → Matrix (Fin 2) (Fin 2) ℂ
| PauliBasis.I => sigmaI
| PauliBasis.X => sigmaX
| PauliBasis.Y => sigmaY
| PauliBasis.Z => sigmaZ
