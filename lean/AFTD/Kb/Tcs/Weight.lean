import AFTD.Prelude
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.Support

/-!
# weight

Topic: quantum   Node: a7274be9499f

Provenance: formalization of a published result. Source: TCSlib, `weight`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{support} $\mathrm{supp}(p) \subseteq \mathrm{Fin}\,n$ consists of coordinates
where $p(i) \neq I$; the \emph{weight} is $\mathrm{wt}(p) = |\mathrm{supp}(p)|$.
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
/-- The weight of a Pauli string: the number of non-identity tensor factors. -/
noncomputable def weight {n : ℕ} (p : PauliString n) : ℕ :=
  (support p).card
