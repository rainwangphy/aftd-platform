import AFTD.Prelude

/-!
# GeneralizedPerspectiveFunction.hpow_continuousOn

Topic: quantum   Node: c3ea9590cd33

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.hpow_continuousOn`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GeneralizedPerspectiveFunction.hpow_continuousOn
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
lemma GeneralizedPerspectiveFunction.hpow_continuousOn
    (h : ℝ → ℝ) (p : ℝ)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    ContinuousOn (fun x : ℝ ↦ (h x) ^ p) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hg : ContinuousWithinAt (fun y : ℝ ↦ y ^ p) (Set.Ioi (0 : ℝ)) (h x) :=
    (Real.continuousAt_rpow_const (h x) p (Or.inl (ne_of_gt (hpos x hx)))).continuousWithinAt
  exact hg.comp (hcont x hx) (by
    intro y hy
    exact hpos y hy)
