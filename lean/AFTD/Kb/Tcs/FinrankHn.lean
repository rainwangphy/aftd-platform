import AFTD.Prelude
import AFTD.Kb.Tcs.Hn

/-!
# finrank_Hn

Topic: quantum   Node: e45025bfb43f

Provenance: helper lemma. TCSlib, `finrank_Hn`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

Complex dimension of the $n$-qubit space. For every natural number $n$, the $n$-qubit Hilbert space $\mathcal{H}_n$ has complex
dimension $\dim_{\mathbb{C}}(\mathcal{H}_n) = 2^n$.
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
/-- The n-qubit Hilbert space `Hn n` has complex dimension 2^n. -/
lemma finrank_Hn (n : ℕ) : Module.finrank ℂ (Hn n) = 2^n := by
  classical
  simp [Hn, finrank_euclideanSpace, Fintype.card_fin]
