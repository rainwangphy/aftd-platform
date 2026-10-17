import AFTD.Prelude
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProj
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumEquiv

/-!
# JensenOperatorInequality.hsumIncl

Topic: quantum   Node: b917950e4819

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.hsumIncl`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `i`-th coordinate inclusion `ℋ →L[ℂ] HSum ℋ`, embedding `ℋ` as the `i`-th summand of the Hilbert sum and placing `0` in the other summand.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
/-- The `i`-th coordinate inclusion `ℋ →L[ℂ] HSum ℋ`, embedding `ℋ` as the `i`-th summand of the Hilbert sum and placing `0` in the other summand. -/
noncomputable def JensenOperatorInequality.hsumIncl (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (i : Fin 2) : ℋ →L[ℂ] HSum ℋ :=
  (hsumEquiv ℋ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.single ℂ (fun _ : Fin 2 => ℋ) i)
