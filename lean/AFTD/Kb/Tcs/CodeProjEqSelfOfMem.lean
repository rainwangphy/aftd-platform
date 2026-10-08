import AFTD.Prelude
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.CodeProj

/-!
# codeProj_eq_self_of_mem

Topic: quantum   Node: 5173abe95f87

Provenance: helper lemma. TCSlib, `codeProj_eq_self_of_mem`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

Projection onto a code fixes its own vectors. Let $C$ be a subspace of the $n$-qubit Hilbert space $\mathcal{H}_n$, and let $P_C :
\mathcal{H}_n \to \mathcal{H}_n$ be the orthogonal projection onto $C$. If $x \in C$,
then $P_C x = x$.
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
lemma codeProj_eq_self_of_mem {n : ℕ} {C : Submodule ℂ (Hn n)} {x : Hn n} (hx : x ∈ C) :
    codeProj C x = x := by

  have h_proj : ∀ x : Hn n, x ∈ C → Submodule.orthogonalProjection C x = x := by
    intros x hx
    apply Submodule.starProjection_eq_self_iff.mpr hx;
  apply h_proj; assumption
