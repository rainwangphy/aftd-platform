import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.RE
import AFTD.Kb.Tcs.SymForm

/-!
# sym_form_r_E

Topic: quantum   Node: 9139e1b86529

Provenance: helper lemma. TCSlib, `sym_form_r_E`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Symplectic form is unchanged by restricting the second argument. Fix a prime $p$ and an integer $n$, and work in the space $V = \bbf_p^{\,n} \times
\bbf_p^{\,n}$ equipped with the symplectic form $\omega$. Let $M \subseteq \{0, 1,
\dots, n-1\}$ be a set of coordinates, and let $v \in V_M$, so that every coordinate of
$v$ lying outside $M$ vanishes. Then for every $s \in V$,
\[
\omega(v, s) = \omega(v, r_M(s)),
\]
where $r_M(s)$ is the vector obtained from $s$ by zeroing out all coordinates outside
$M$.
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
/-- Symplectic form respects restriction -/
lemma sym_form_r_E (M : Finset (Fin n)) (v : V n p) (hv : v ∈ V_sub (p:=p) M) (s : V n p) :
    sym_form v s = sym_form v (r_E M s) := by
      refine' Finset.sum_congr rfl fun i hi => _;
      by_cases hi' : i ∈ M <;> simp_all +decide [ r_E ];
      cases hv i hi' ; simp_all only [zero_mul, sub_self]
