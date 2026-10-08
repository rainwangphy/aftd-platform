import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.SymForm

/-!
# sym_form_swap

Topic: quantum   Node: e5821ae19243

Provenance: helper lemma. TCSlib, `sym_form_swap`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Antisymmetry of the symplectic form. Fix a prime $p$ and an integer $n$, and equip $V = \bbf_p^n \times \bbf_p^n$ with the
bilinear form $\omega(u,v) = \sum_{i=0}^{n-1}(x_i z'_i - z_i x'_i)$, where $u = (x,z)$
and $v = (x',z')$. Then $\omega$ is antisymmetric: for all $u, v \in V$, \[ \omega(u,v)
= -\,\omega(v,u). \]
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
/-- The symplectic form is antisymmetric: `sym_form u v = -sym_form v u`. -/
lemma sym_form_swap (u v : V n p) :
    sym_form u v = - sym_form v u := by
  unfold sym_form
  rw [← Finset.sum_neg_distrib]
  congr with i
  ring
