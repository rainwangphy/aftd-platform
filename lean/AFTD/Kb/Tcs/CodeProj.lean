import AFTD.Prelude
import AFTD.Kb.Tcs.Hn

/-!
# codeProj

Topic: quantum   Node: 40e85b7626b8

Provenance: formalization of a published result. Source: TCSlib, `codeProj`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

The orthogonal projection of $\mathcal{H}_n$ onto a subspace $C$, viewed as an endomorphism
$P_C : \mathcal{H}_n \to \mathcal{H}_n$.
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
/-- The orthogonal projection from `Hn n` onto the code subspace `C`, viewed as an endomorphism. -/
noncomputable def codeProj {n : ℕ} (C : Submodule ℂ (Hn n)) : Hn n →ₗ[ℂ] Hn n :=
  (C.subtypeL.comp (Submodule.orthogonalProjection C)).toLinearMap
