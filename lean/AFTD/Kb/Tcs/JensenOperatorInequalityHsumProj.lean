import AFTD.Prelude
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumEquiv

/-!
# JensenOperatorInequality.hsumProj

Topic: quantum   Node: 0c2f4946b746

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.hsumProj`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `i`-th coordinate projection `HSum ℋ →L[ℂ] ℋ` of the Hilbert sum onto its `i`-th summand.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
/-- The `i`-th coordinate projection `HSum ℋ →L[ℂ] ℋ` of the Hilbert sum onto its `i`-th summand. -/
noncomputable def JensenOperatorInequality.hsumProj (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (i : Fin 2) : HSum ℋ →L[ℂ] ℋ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℋ) i) ∘L
    (hsumEquiv ℋ).toContinuousLinearMap
