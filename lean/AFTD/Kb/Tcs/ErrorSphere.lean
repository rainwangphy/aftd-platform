import AFTD.Prelude
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.PauliErrorsLe
import AFTD.Kb.Tcs.PauliOp
import AFTD.Kb.Tcs.CodeProjApply
import AFTD.Kb.Tcs.InstFintypePauliString
import AFTD.Kb.Tcs.InstFiniteDimensionalComplexSubtypeHnMemSubmodule
import AFTD.Kb.Tcs.Weight

/-!
# ErrorSphere

Topic: quantum   Node: f92e41c379cc

Provenance: formalization of a published result. Source: TCSlib, `ErrorSphere`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{error sphere} $\mathrm{ES}(C,t)$ is the subspace
$\bigvee_{\mathrm{wt}(p)\le t} \hat{p}(C)$, i.e.\ the supremum of the
Pauli images of $C$ over all $t$-errors.
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
/-- The error sphere: the span of all images `E(C)` over Pauli strings `E` of weight ≤ t. This is the subspace that must fit inside `Hn n` to derive the Hamming bound. -/
noncomputable def ErrorSphere (n t : ℕ) (C : Submodule ℂ (Hn n)) : Submodule ℂ (Hn n) :=
  (PauliErrorsLe n t).sup (fun E => C.map (pauliOp E))
