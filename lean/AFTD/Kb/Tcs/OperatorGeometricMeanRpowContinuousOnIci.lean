import AFTD.Prelude

/-!
# OperatorGeometricMean.rpow_continuousOn_Ici

Topic: quantum   Node: 685612a26a5a

Provenance: formalization of a published result. Source: QuantumInfo, `OperatorGeometricMean.rpow_continuousOn_Ici`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/OperatorGeometricMean.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

OperatorGeometricMean.rpow_continuousOn_Ici
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
lemma OperatorGeometricMean.rpow_continuousOn_Ici (p : ℝ) (hp : 0 ≤ p) :
    ContinuousOn (fun x : ℝ ↦ x ^ p) (Set.Ici (0 : ℝ)) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x p (Or.inr hp)).continuousWithinAt
