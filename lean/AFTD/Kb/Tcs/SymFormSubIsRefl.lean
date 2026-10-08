import AFTD.Prelude
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.SymForm
import AFTD.Kb.Tcs.SymFormSub
import AFTD.Kb.Tcs.SymFormSubApply
import AFTD.Kb.Tcs.SymFormSwap

/-!
# sym_form_sub_isRefl

Topic: quantum   Node: 312692550e21

Provenance: helper lemma. TCSlib, `sym_form_sub_isRefl`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Reflexivity of the restricted symplectic form. Fix a prime $p$, a natural number $n$, and a subset $M \subseteq \{0,1,\dots,n-1\}$, and
let $V_M$ be the associated support submodule of $V = \bbf_p^{\,n} \times \bbf_p^{\,n}$.
Then the restriction to $V_M$ of the symplectic form $\omega(u,v) = \sum_{i} (x_i z'_i -
z_i x'_i)$, where $u=(x,z)$ and $v=(x',z')$, is reflexive: for all $u, v \in V_M$, if
$\omega(u,v) = 0$ then $\omega(v,u) = 0$.
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
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
/-- The restricted symplectic form is reflexive -/
lemma sym_form_sub_isRefl (M : Finset (Fin n)) :
    (sym_form_sub (n:=n) (p:=p) M).IsRefl := by
  intro v w h
  have h' :
      sym_form (n:=n) (p:=p) (v : V n p) (w : V n p) = 0 := by
    simpa [sym_form_sub_apply] using h

  have hwv :
      sym_form (n:=n) (p:=p) (w : V n p) (v : V n p) = 0 := by
    calc
      sym_form (n:=n) (p:=p) (w : V n p) (v : V n p)
          = - sym_form (n:=n) (p:=p) (v : V n p) (w : V n p) := by
              simpa using
                (sym_form_swap (n:=n) (p:=p)
                  (u := (w : V n p)) (v := (v : V n p)))
      _ = 0 := by simpa [h']

  -- go back down to the restricted form
  simpa [sym_form_sub_apply] using hwv

/-
Dimension of S^\perp \cap V_M is 2|M| - dim(r_M(S)).
-/
