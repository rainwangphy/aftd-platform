import AFTD.Prelude

/-!
# JensenOperatorInequality.continuousOn_union_of_subset_Ici_wrap

Topic: quantum   Node: 74f140c04e77

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.continuousOn_union_of_subset_Ici_wrap`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequality.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.continuousOn_union_of_subset_Ici_wrap
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
lemma JensenOperatorInequality.continuousOn_union_of_subset_Ici_wrap {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ))) {s t : Set ℝ}
    (hs : s ⊆ Set.Ici (0 : ℝ)) (ht : t ⊆ Set.Ici (0 : ℝ)) :
    ContinuousOn f (s ∪ t) := by
  refine hcont.mono ?_
  intro x hx
  rcases hx with hx | hx
  · exact hs hx
  · exact ht hx
