import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.VSubIso

/-!
# dim_V_sub

Topic: quantum   Node: 833391619485

Provenance: helper lemma. TCSlib, `dim_V_sub`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Dimension of the support submodule. Fix a prime $p$ and an integer $n$, and let $V = \bbf_p^{\,n} \times \bbf_p^{\,n}$ be
the space of pairs of coordinate vectors over the prime field $\bbf_p$. For a subset $C
\subseteq \{1, \dots, n\}$, let $V_C \subseteq V$ be the support submodule consisting of
those pairs $(u, w)$ for which $u_i = 0$ and $w_i = 0$ at every index $i \notin C$. Then
$V_C$ has dimension $\dim_{\bbf_p}(V_C) = 2\lvert C\rvert$ over $\bbf_p$.
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
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
lemma dim_V_sub (C : Finset (Fin n)) : Module.finrank (F p) (V_sub (p:=p) C) = 2 * C.card := by
  classical
  -- finrank preserved by linear equivalence
  simpa [Module.finrank_prod, two_mul] using
    (LinearEquiv.finrank_eq (V_sub_iso (n:=n) (p:=p) C))


/-
Definition of restriction map r_E.
-/
