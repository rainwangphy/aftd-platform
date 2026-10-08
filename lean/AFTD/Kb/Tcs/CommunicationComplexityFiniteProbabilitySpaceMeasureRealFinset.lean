import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceMeasureRealPreimageFinset

/-!
# CommunicationComplexity.FiniteProbabilitySpace.measureReal_finset

Topic: communication   Node: b90095034613

Provenance: helper lemma. TCSlib, `CommunicationComplexity.FiniteProbabilitySpace.measureReal_finset`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Additivity of the measure over a finite set. Let $\Omega$ be a finite probability space, and let $T$ be a finite subset of $\Omega$.
Writing $\mathbb{P}$ for the real-valued probability measure on $\Omega$, the measure of
$T$ is the sum of the measures of its singletons:
\[
  \mathbb{P}(T) \;=\; \sum_{a \in T} \mathbb{P}(\{a\}).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
/-- The real-valued measure of a finite set splits as a sum over its singleton parts. -/
theorem CommunicationComplexity.FiniteProbabilitySpace.measureReal_finset
    {Ω : Type*} [FiniteProbabilitySpace Ω] (T : Finset Ω) :
    volume.real (↑T : Set Ω) = ∑ a ∈ T, volume.real ({a} : Set Ω) := by
  exact measureReal_preimage_finset id T
