import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.SymForm

/-!
# sym_form_nondegenerate

Topic: quantum   Node: bcc149919ed1

Provenance: helper lemma. TCSlib, `sym_form_nondegenerate`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Nondegeneracy of the symplectic form. Let $p$ be a prime and $n \ge 0$, and let $\omega$ be the symplectic form on $V =
\bbf_p^n \times \bbf_p^n$. If a vector $u \in V$ satisfies $\omega(u,v) = 0$ for every
$v \in V$, then $u = 0$.
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
/-- The symplectic form is non-degenerate: if `sym_form u v = 0` for all `v`, then `u = 0`. -/
lemma sym_form_nondegenerate (u : V n p) (h : ∀ v, sym_form u v = 0) : u = 0 := by
  have h_cases : ∀ (i : Fin n), u.1 i = 0 ∧ u.2 i = 0 := by
    intro i
    have h1 : u.1 i = 0 := by
      specialize h ⟨ 0, fun j => if j = i then 1 else 0 ⟩ ; simp_all +decide [ sym_form ] ;
    have h2 : u.2 i = 0 := by
      specialize h ⟨ fun j => if j = i then 1 else 0, 0 ⟩ ; simp_all +decide [ sym_form ] ;
    exact ⟨h1, h2⟩;
  exact Prod.ext ( funext fun i => h_cases i |>.1 ) ( funext fun i => h_cases i |>.2 )

/-
Definition of support, weight, and support subspace V_C.
-/
