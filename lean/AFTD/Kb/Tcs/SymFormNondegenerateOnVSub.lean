import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.RE
import AFTD.Kb.Tcs.SymForm
import AFTD.Kb.Tcs.SymFormNondegenerate
import AFTD.Kb.Tcs.SymFormRE

/-!
# sym_form_nondegenerate_on_V_sub

Topic: quantum   Node: 905e61cfdf69

Provenance: helper lemma. TCSlib, `sym_form_nondegenerate_on_V_sub`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Non-degeneracy of the symplectic form on a support submodule. Let $p$ be a prime, let $n$ be a natural number, and let $M \subseteq \{0,1,\dots,n-1\}$
be a subset of coordinates. Write $V = \mathbb{F}_p^n \times \mathbb{F}_p^n$ for the
symplectic space equipped with the form $\omega\big((x,z),(x',z')\big) =
\sum_{i=0}^{n-1}(x_i z'_i - z_i x'_i)$, and let $V_M \subseteq V$ be the support
submodule of those vectors whose coordinates outside $M$ all vanish. If $v \in V_M$
satisfies $\omega(v,w) = 0$ for every $w \in V_M$, then $v = 0$.
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
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
/-- Non-degeneracy on V_sub M -/
lemma sym_form_nondegenerate_on_V_sub (M : Finset (Fin n)) (v : V n p)
    (hv : v ∈ V_sub (p:=p) M)
    (h : ∀ w : V n p, w ∈ V_sub (p:=p) M → sym_form (n:=n) (p:=p) v w = 0) :
    v = 0 := by
  apply sym_form_nondegenerate (n:=n) (p:=p) v
  intro w
  have hw0 :
      sym_form (n:=n) (p:=p) v (↑(r_E (n:=n) (p:=p) M w) : V n p) = 0 :=
    h (↑(r_E (n:=n) (p:=p) M w) : V n p)
      (by simpa using (r_E (n:=n) (p:=p) M w).property)
  simpa [sym_form_r_E (n:=n) (p:=p) M v hv w] using hw0


/-
Intersection of S^\perp with V_M is the same as intersection of (r_M(S))^\perp with V_M.
-/
