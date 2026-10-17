import AFTD.Prelude
import AFTD.Kb.Tcs.JensenOperatorInequalityHSum

/-!
# JensenOperatorInequality.hsumEquiv

Topic: quantum   Node: f9907235f6d7

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.hsumEquiv`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/BlockDiagonal.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The continuous linear equivalence between the Hilbert sum `HSum ℋ` and the plain function space `Fin 2 → ℋ`, forgetting the `ℓ²` inner-product structure on the index.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open JensenOperatorInequality in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
/-- The continuous linear equivalence between the Hilbert sum `HSum ℋ` and the plain function space `Fin 2 → ℋ`, forgetting the `ℓ²` inner-product structure on the index. -/
noncomputable def JensenOperatorInequality.hsumEquiv (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] :
    HSum ℋ ≃L[ℂ] (Fin 2 → ℋ) :=
  PiLp.continuousLinearEquiv (p := (2 : ENNReal)) (𝕜 := ℂ) (β := fun _ : Fin 2 => ℋ)
