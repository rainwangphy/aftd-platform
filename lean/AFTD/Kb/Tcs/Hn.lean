import AFTD.Prelude

/-!
# Hn

Topic: quantum   Node: 0245eab30653

Provenance: formalization of a published result. Source: TCSlib, `Hn`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

The $n$-qubit Hilbert space
$\mathcal{H}_n = \ell^2\!\bigl(\{0,1\}^n,\mathbb{C}\bigr)$,
implemented as \texttt{EuclideanSpace ℂ (Fin n → Fin 2)}.
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
/-- The n-qubit Hilbert space ℂ^(2^n), realized as a Euclidean space indexed by `Fin n → Fin 2`. -/
noncomputable abbrev Hn (n : ℕ) := EuclideanSpace ℂ (Fin n → Fin 2)
