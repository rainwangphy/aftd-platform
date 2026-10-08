import AFTD.Prelude
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.CodeProj

/-!
# codeProj_apply

Topic: quantum   Node: 29bb5cd0c6ef

Provenance: helper lemma. TCSlib, `codeProj_apply`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

Action of the code projection. Let $C$ be a closed subspace of the $n$-qubit Hilbert space $\mathcal{H}_n$, and let
$P_C : \mathcal{H}_n \to \mathcal{H}_n$ be the associated orthogonal projection onto
$C$. Then for every $x \in \mathcal{H}_n$, the value $P_C\,x$ is exactly the orthogonal
projection of $x$ onto $C$.
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
@[simp] lemma codeProj_apply {n : ℕ} (C : Submodule ℂ (Hn n)) (x : Hn n) :
    codeProj C x = (Submodule.orthogonalProjection C x : Hn n) := by
  simp [codeProj]
