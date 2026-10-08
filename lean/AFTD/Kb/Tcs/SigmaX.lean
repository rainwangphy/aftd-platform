import AFTD.Prelude

/-!
# sigmaX

Topic: quantum   Node: 63245678aa6f

Provenance: formalization of a published result. Source: TCSlib, `sigmaX`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

The bit-flip Pauli matrix
$X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$
over $\mathbb{C}$.
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
/-- The bit-flip Pauli matrix X = [[0,1],[1,0]] over ℂ. -/
noncomputable def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
