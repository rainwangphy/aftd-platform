import AFTD.Prelude
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.SymForm
import AFTD.Kb.Tcs.SymFormNondegenerateOnVSub
import AFTD.Kb.Tcs.SymFormSub
import AFTD.Kb.Tcs.SymFormSubApply

/-!
# sym_form_sub_nondegenerate

Topic: quantum   Node: f25f4e531fde

Provenance: helper lemma. TCSlib, `sym_form_sub_nondegenerate`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 adapted; compiled here.

Nondegeneracy of the restricted symplectic form. Let $p$ be a prime, and equip $V = \bbf_p^n \times \bbf_p^n$ with the symplectic form
$\omega\big((x,z),(x',z')\big) = \sum_{i=0}^{n-1}(x_i z'_i - z_i x'_i)$. For any subset
$M \subseteq \{0,\dots,n-1\}$, let $V_M$ be the support submodule consisting of those
$(x,z) \in V$ with $x_i = z_i = 0$ for every $i \notin M$. Then the restriction of
$\omega$ to $V_M$ is nondegenerate: if $u \in V_M$ satisfies $\omega(u,v) = 0$ for all
$v \in V_M$, then $u = 0$.
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
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
/-- Non-degeneracy of restricted form -/
lemma sym_form_sub_nondegenerate (M : Finset (Fin n)) :
    (sym_form_sub (p:=p) M).Nondegenerate := by
      refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft ?_
      intro v hv
      apply Classical.byContradiction
      intro hv_nonzero;
      obtain ⟨w, hw⟩ : ∃ w : V_sub (p:=p) M, sym_form v.1 w.1 ≠ 0 := by
        convert sym_form_nondegenerate_on_V_sub M v.1 v.2 using 1;
        simp +zetaDelta at *;
        grind;
      exact hw ( hv w )

/-
S^\perp \cap V_M is the image of the orthogonal complement of r_M(S) in V_M.
-/
