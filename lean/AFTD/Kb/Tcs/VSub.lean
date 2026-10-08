import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.V

/-!
# V_sub

Topic: quantum   Node: 90bec3c1636b

Provenance: formalization of a published result. Source: TCSlib, `V_sub`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

For $C \subseteq \mathrm{Fin}\,n$, the \emph{support submodule}
$V_C = \{v \in V \mid \mathrm{supp}(v) \subseteq C\}$.
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
/-- Support subspace V_C -/
noncomputable def V_sub (C : Finset (Fin n)) : Submodule (F p) (V n p) where
  carrier := {v | ∀ i ∉ C, v.1 i = 0 ∧ v.2 i = 0}
  add_mem' := by
    intro a b a_1 a_2
    simp_all only [Set.mem_setOf_eq, Prod.fst_add, Pi.add_apply, not_false_eq_true, add_zero, Prod.snd_add, and_self,
      implies_true]
  zero_mem' := by
    simp_all only [Set.mem_setOf_eq, Prod.fst_zero, Pi.zero_apply, Prod.snd_zero, and_self, implies_true]
  smul_mem' := by
    intro c x a
    simp_all only [Set.mem_setOf_eq, Prod.smul_fst, Pi.smul_apply, not_false_eq_true, smul_eq_mul, mul_zero,
      Prod.smul_snd, and_self, implies_true]

/-
Isomorphism between V_C and F^|C| x F^|C|.
-/
