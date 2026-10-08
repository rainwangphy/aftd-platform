import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.OrthInterEqOrthMap
import AFTD.Kb.Tcs.RE
import AFTD.Kb.Tcs.REV
import AFTD.Kb.Tcs.SymB
import AFTD.Kb.Tcs.SymFormSub
import AFTD.Kb.Tcs.SymOrth
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymFormSubApply

/-!
# orth_inter_eq_orth_sub_image

Topic: quantum   Node: 31de15841f3f

Provenance: helper lemma. TCSlib, `orth_inter_eq_orth_sub_image`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 adapted; compiled here.

Orthogonal complement of a subspace, intersected with a support submodule. Let $p$ be a prime and let $\omega$ be the symplectic form on $V = \bbf_p^{\,n} \times
\bbf_p^{\,n}$. For any subset $M$ of $\{0, 1, \dots, n-1\}$ and any submodule $S \le V$,
the vectors of the support submodule $V_M$ that are $\omega$-orthogonal to every element
of $S$ are exactly the images, under the inclusion $V_M \hookrightarrow V$, of the
vectors of $V_M$ that are orthogonal to $r_M(S)$ with respect to the restriction of
$\omega$ to $V_M$. In symbols, writing $\iota \colon V_M \hookrightarrow V$ for the
inclusion and $\perp_M$ for orthogonality with respect to the restricted form,
\[
S^{\perp_\omega} \cap V_M \;=\; \iota\!\left( r_M(S)^{\perp_M} \right),
\]
where $r_M(S)$ is the image of $S$ under the restriction map $r_M \colon V \to V_M$.
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
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
/-- The intersection S^\perp ∩ V_M corresponds to the orthogonal complement of r_M(S) in V_M -/
lemma orth_inter_eq_orth_sub_image (M : Finset (Fin n)) (S : Submodule (F p) (V n p)) :
    sym_orth S ⊓ V_sub (p:=p) M = ((sym_form_sub (p:=p) M).orthogonal (S.map (r_E M))).map (V_sub (p:=p) M).subtype := by
  classical
  convert orth_inter_eq_orth_map M S using 1;
  ext; simp [sym_form_sub];
  try simp +decide [ symB, LinearMap.BilinForm.IsOrtho ];
  simp +decide [ r_E_V, Subtype.ext_iff ];
  grind


/-
The restricted symplectic form is reflexive.
-/
