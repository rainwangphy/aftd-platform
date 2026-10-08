import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.SymForm
import AFTD.Kb.Tcs.SymFormSub

/-!
# sym_form_sub_apply

Topic: quantum   Node: 9ed59bc2b848

Provenance: helper lemma. TCSlib, `sym_form_sub_apply`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Evaluation of the restricted symplectic form. Fix a prime $p$ and let $\omega$ denote the symplectic form on $V = \bbf_p^{\,n} \times
\bbf_p^{\,n}$. For a subset $M \subseteq \{0, \dots, n-1\}$ and any two vectors $x, y$
in the support submodule $V_M$, the restricted symplectic form evaluated at $(x, y)$
agrees with $\omega(x, y)$ computed on $x$ and $y$ regarded as elements of the ambient
space $V$.
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
@[simp] lemma sym_form_sub_apply (M : Finset (Fin n))
    (x y : ↥(V_sub (p:=p) M)) :
    sym_form_sub (n:=n) (p:=p) M x y
      = sym_form (n:=n) (p:=p) (x : V n p) (y : V n p) := rfl

/-
The restricted symplectic form is non-degenerate.
-/
