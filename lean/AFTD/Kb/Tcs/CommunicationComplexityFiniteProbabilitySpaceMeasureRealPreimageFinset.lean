import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.FiniteProbabilitySpace.measureReal_preimage_finset

Topic: communication   Node: d4f1c2b64a9f

Provenance: helper lemma. TCSlib, `CommunicationComplexity.FiniteProbabilitySpace.measureReal_preimage_finset`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Measure of a preimage of a finite set. Let $\Xi$ be a finite probability space and let $\Omega$ be a measurable space in which
every subset is measurable. For any map $\varphi \colon \Xi \to \Omega$ and any finite
set $T \subseteq \Omega$, the probability that $\varphi$ lands in $T$ decomposes as a
sum over the points of $T$:
\[
  \mathrm{volume}^{\mathbb{R}}\bigl(\varphi^{-1}(T)\bigr)
  \;=\; \sum_{a \in T} \mathrm{volume}^{\mathbb{R}}\bigl(\varphi^{-1}(\{a\})\bigr),
\]
where $\mathrm{volume}^{\mathbb{R}}$ denotes the real-valued measure of the underlying
probability measure on $\Xi$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
/-- The real-valued measure of the preimage of a finite set splits as a sum over singleton fibers. -/
theorem CommunicationComplexity.FiniteProbabilitySpace.measureReal_preimage_finset
    {Ξ Ω : Type*} [FiniteProbabilitySpace Ξ]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (φ : Ξ → Ω) (T : Finset Ω) :
    volume.real (φ ⁻¹' (↑T : Set Ω) : Set Ξ) =
      ∑ a ∈ T, volume.real (φ ⁻¹' ({a} : Set Ω) : Set Ξ) := by
  rw [Measure.real]
  rw [show (φ ⁻¹' (↑T : Set Ω) : Set Ξ) = ⋃ a ∈ T, φ ⁻¹' ({a} : Set Ω) from by
    ext ξ
    simp]
  rw [measure_biUnion_finset
    (fun a _ b _ h => Disjoint.preimage _ (Set.disjoint_singleton.mpr h))
    (fun _ _ => MeasurableSet.of_discrete)]
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp [Measure.real]
