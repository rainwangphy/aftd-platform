import AFTD.Prelude

/-!
# CommunicationComplexity.TVDistance.totalVariation_real_univ

Topic: information   Node: bf6c52bb2446

Provenance: helper lemma. TCSlib, `CommunicationComplexity.TVDistance.totalVariation_real_univ`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Total variation mass as the sum of Jordan parts. Let $s$ be a signed measure on a measurable space $\Omega$, with Jordan decomposition $s
= s^+ - s^-$ into its positive and negative parts $s^+$ and $s^-$. Then the total mass
of the total variation measure $\abs{s}$ of $s$, taken as a real number, is the sum of
the total masses of the two Jordan parts:
\[
\abs{s}(\Omega) = s^+(\Omega) + s^-(\Omega).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- The total mass of the total variation of a signed measure is `P(Ω) + N(Ω)` for its Jordan decomposition. -/
lemma CommunicationComplexity.TVDistance.totalVariation_real_univ
    {Ω : Type*} [MeasurableSpace Ω] (s : SignedMeasure Ω) :
    s.totalVariation.real Set.univ =
      s.toJordanDecomposition.posPart.real Set.univ +
        s.toJordanDecomposition.negPart.real Set.univ := by
  rw [SignedMeasure.totalVariation, measureReal_add_apply]
