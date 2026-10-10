import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapHasDenseDomain
import AFTD.Kb.Physics.LinearPMapIsSymmetricDef
import AFTD.Kb.Physics.LinearPMapIsSymmetricIffLeAdjoint
import AFTD.Kb.Physics.LinearPMapAdjointAntitone
import AFTD.Kb.Physics.LinearPMapIsSymmetricOfLe
import AFTD.Kb.Physics.LinearPMapIsClosedClosureEq
import AFTD.Kb.Physics.LinearPMapHasDenseDomainClosure

/-!
# LinearPMap.IsSymmetric.closure

Topic: quantum_mechanics   Node: c0b195a34e95

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.closure`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The closure of a symmetric densely-defined operator is symmetric: `T††` is a symmetric closed extension of `T`, so it extends `T.closure`, whose symmetry then descends.
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
variable (u : H ≃ₗᵢ[ℂ] H') (A : H →ₗ.[ℂ] H) in
variable {u A} in
/-- The closure of a symmetric densely-defined operator is symmetric: `T††` is a symmetric closed extension of `T`, so it extends `T.closure`, whose symmetry then descends. -/
lemma LinearPMap.IsSymmetric.closure [CompleteSpace H] (hsym : T.IsSymmetric) (hdense : T.HasDenseDomain) :
    T.closure.IsSymmetric := by
  have hle : T ≤ T† := (isSymmetric_def.mp hsym).le_adjoint hdense
  have hadj_dense : T†.HasDenseDomain := hdense.mono hle.1
  have hT_le : T ≤ T†† := (adjoint_isFormalAdjoint hdense).le_adjoint hadj_dense
  have hc : (T††).IsClosed := adjoint_isClosed hadj_dense
  have h1 : (T††).IsSymmetric :=
    (isSymmetric_iff_le_adjoint (hdense.mono hT_le.1)).mpr
      (adjoint_antitone (Or.inl (hdense.mono hT_le.1)) (adjoint_antitone (Or.inl hdense) hle))
  exact h1.of_le (hc.closure_eq ▸ hc.isClosable.closure_mono hT_le)
