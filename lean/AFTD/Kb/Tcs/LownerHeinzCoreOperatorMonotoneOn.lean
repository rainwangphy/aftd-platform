import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzCoreCfcR

/-!
# LownerHeinzCore.OperatorMonotoneOn

Topic: quantum   Node: ba01e58c561c

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzCore.OperatorMonotoneOn`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fixed-space operator monotonicity on `s` for the ambient algebra `𝓐`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LownerHeinzCore in
universe u v in
open CFC in
variable {𝓐 : Type u} in
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] in
variable [Nontrivial 𝓐] in
/-- Fixed-space operator monotonicity on `s` for the ambient algebra `𝓐`. -/
def LownerHeinzCore.OperatorMonotoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄,
    0 ≤ A → 0 ≤ B → B ≤ A →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    cfcR f B ≤ cfcR f A
