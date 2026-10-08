import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.Supp

/-!
# wt

Topic: quantum   Node: 910984de406f

Provenance: formalization of a published result. Source: TCSlib, `wt`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{support} $\mathrm{supp}(v) \subseteq \mathrm{Fin}\,n$ consists of
coordinates where either component of $v$ is nonzero;
the \emph{weight} is $\mathrm{wt}(v) = |\mathrm{supp}(v)|$.
-/

open scoped BigOperators in
set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
set_option linter.unnecessarySimpa false in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
/-- Weight of a vector v in V -/
noncomputable def wt (v : V n p) : ℕ := (supp v).card
