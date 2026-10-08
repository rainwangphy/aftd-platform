import AFTD.Prelude

/-!
# CommunicationComplexity.uniformOn_univ_measureReal_eq_card_filter

Topic: communication   Node: 92a7bc415748

Provenance: helper lemma. TCSlib, `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_filter`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Uniform measure of a set equals its relative cardinality. Let $\Omega$ be a nonempty finite set, equipped with the uniform probability measure
that assigns each point mass $1/\abs{\Omega}$, and let $S \subseteq \Omega$. Then the
measure of $S$, as a real number, is
\[
  \frac{\abs{\{\omega \in \Omega \mid \omega \in S\}}}{\abs{\Omega}},
\]
the number of elements of $\Omega$ lying in $S$ divided by the total number of elements
of $\Omega$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
open Classical in
/-- On a finite discrete type with the uniform measure on `Set.univ`, the real-valued measure of a set is its cardinality divided by the size of the ambient type. -/
theorem CommunicationComplexity.uniformOn_univ_measureReal_eq_card_filter
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] (S : Set Ω) :
    ((ProbabilityTheory.uniformOn Set.univ : Measure Ω) S).toReal =
      ((Finset.univ.filter fun ω : Ω => ω ∈ S).card : ℝ) / Fintype.card Ω := by
  rw [ProbabilityTheory.uniformOn_univ, ENNReal.toReal_div,
    Measure.count_apply MeasurableSet.of_discrete,
    Set.encard_eq_coe_toFinset_card]
  simp [ENat.toENNReal_coe, ENNReal.toReal_natCast]
