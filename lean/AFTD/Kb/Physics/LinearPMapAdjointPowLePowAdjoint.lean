import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.LinearPMapInstMonoid
import AFTD.Kb.Physics.LinearPMapAdjointOne
import AFTD.Kb.Physics.LinearPMapPowHasDenseDomainOfLe
import AFTD.Kb.Physics.LinearPMapCompRestricted
import AFTD.Kb.Physics.LinearPMapCompRestrictedAssoc
import AFTD.Kb.Physics.LinearPMapCompRestrictedMonoRight
import AFTD.Kb.Physics.LinearPMapAdjointCompRestrictedLeCompRestrictedAdjoint
import AFTD.Kb.Physics.LinearPMapSumApply

/-!
# LinearPMap.adjoint_pow_le_pow_adjoint

Topic: quantum_mechanics   Node: 01d33a709caa

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.adjoint_pow_le_pow_adjoint`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.adjoint_pow_le_pow_adjoint
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
open InnerProductSpace in
open Complex ComplexConjugate in
variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
  {α : Type*} [Fintype α]
  {T T₁ T₂ : H →ₗ.[ℂ] H} {S : α → H →ₗ.[ℂ] H}
  {U U₁ U₂ : H →ₗ.[ℂ] H'} {W : α → H →ₗ.[ℂ] H'}
  {V V₁ V₂ : H' →ₗ.[ℂ] H''} in
lemma LinearPMap.adjoint_pow_le_pow_adjoint [CompleteSpace H] {n : ℕ} (h : (T ^ n).HasDenseDomain) :
    T† ^ n ≤ (T ^ n)† := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hTn : (T ^ n).HasDenseDomain := pow_hasDenseDomain_of_le h n.le_succ
    refine le_trans ?_ (adjoint_compRestricted_le_compRestricted_adjoint hTn h)
    exact pow_succ' T† n ▸ compRestricted_mono_right T† (ih hTn)
