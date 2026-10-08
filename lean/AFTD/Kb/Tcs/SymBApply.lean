import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.SymB
import AFTD.Kb.Tcs.SymForm

/-!
# symB_apply

Topic: quantum   Node: 435486706bcb

Provenance: helper lemma. TCSlib, `symB_apply`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Evaluation of the bundled symplectic form. Fix a prime $p$ and an integer $n$, and set $V = \bbf_p^n \times \bbf_p^n$, equipped
with the alternating bilinear form
\[
\omega\big((x,z),(x',z')\big) \;=\; \sum_{i=1}^{n}\big(x_i z'_i - z_i x'_i\big),
\qquad (x,z),(x',z') \in V.
\]
Let $B \colon V \times V \to \bbf_p$ be the bilinear form on $V$ obtained by bundling
$\omega$. Then $B$ agrees with $\omega$ on every pair of arguments: for all $u, v \in V$
one has $B(u,v) = \omega(u,v)$.
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
@[simp] lemma symB_apply (x y : V n p) :
    symB (n:=n) (p:=p) x y = sym_form (n:=n) (p:=p) x y := rfl
