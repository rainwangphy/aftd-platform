import AFTD.Prelude
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.Weight
import AFTD.Kb.Tcs.InstFintypePauliString
import AFTD.Kb.Tcs.Support

/-!
# PauliErrorsLe

Topic: quantum   Node: 4e19ed2bc16a

Provenance: formalization of a published result. Source: TCSlib, `PauliErrorsLe`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

The set of all Pauli strings of weight at most $t$:
\[
\mathcal{E}(n,t) = \bigl\{p : \mathrm{PauliString}\,n \;\big|\; \mathrm{wt}(p) \le t\bigr\}.
\]
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
/-- The finset of all n-qubit Pauli strings of weight at most `t`. -/
noncomputable def PauliErrorsLe (n t : ℕ) : Finset (PauliString n) :=
  Finset.filter (fun p => weight p ≤ t) Finset.univ

/-
Counting Paulis: canonical “choose support then assign X/Y/Z” approach.
We introduce a 3-element type for non-identity Paulis.
-/
