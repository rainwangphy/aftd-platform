import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBasis
import AFTD.Kb.Tcs.PauliNZ

/-!
# PauliNZ.toBasis

Topic: quantum   Node: 0d9d4d534be7

Provenance: formalization of a published result. Source: TCSlib, `PauliNZ.toBasis`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

Embeds a non-identity Pauli ($X$, $Y$, or $Z$) from the three-element type
$\mathrm{PauliNZ}$ into the full Pauli basis $\{I,X,Y,Z\}$.
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
/-- Embeds a non-identity Pauli into the full Pauli basis. -/
noncomputable def PauliNZ.toBasis : PauliNZ → PauliBasis
| .X => .X
| .Y => .Y
| .Z => .Z
