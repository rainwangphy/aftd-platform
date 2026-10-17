import AFTD.Prelude

/-!
# OperatorGeometricMean.rpow_pos_on_Ioi

Topic: quantum   Node: 8aab2d5e0618

Provenance: formalization of a published result. Source: QuantumInfo, `OperatorGeometricMean.rpow_pos_on_Ioi`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/OperatorGeometricMean.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

OperatorGeometricMean.rpow_pos_on_Ioi
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
lemma OperatorGeometricMean.rpow_pos_on_Ioi (p : ℝ) :
    ∀ x ∈ Set.Ioi (0 : ℝ), 0 < x ^ p := by
  intro x hx
  exact Real.rpow_pos_of_pos hx p
