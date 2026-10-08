import AFTD.Prelude

/-!
# CommunicationComplexity.TVDistance.signedMeasure_apply_eq_posPart_sub_negPart

Topic: information   Node: ef7689eb248c

Provenance: helper lemma. TCSlib, `CommunicationComplexity.TVDistance.signedMeasure_apply_eq_posPart_sub_negPart`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Signed measure via Jordan decomposition. Let $s$ be a signed measure on a measurable space $\Omega$, and let $s = s^+ - s^-$ be
its Jordan decomposition into a pair of (finite, mutually singular) positive measures
$s^+$ and $s^-$. Then for every measurable set $S \subseteq \Omega$,
\[
s(S) = s^+(S) - s^-(S),
\]
where $s^+(S)$ and $s^-(S)$ denote the real-valued measures of $S$ under the positive
and negative parts.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- A signed measure evaluated on a measurable set is the difference of the (real) masses of the positive and negative parts of its Jordan decomposition. -/
lemma CommunicationComplexity.TVDistance.signedMeasure_apply_eq_posPart_sub_negPart
    {Ω : Type*} [MeasurableSpace Ω] (s : SignedMeasure Ω)
    {S : Set Ω} (hS : MeasurableSet S) :
    s S =
      s.toJordanDecomposition.posPart.real S -
        s.toJordanDecomposition.negPart.real S := by
  conv_lhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition s]
  rw [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hS]
