import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexitySignedMeasureDiff
import AFTD.Kb.Tcs.CommunicationComplexityTvDistance
import AFTD.Kb.Tcs.CommunicationComplexityTvDistanceSup
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceEventAbsMeasureRealSubLeHalfTotalVariation
import AFTD.Kb.Tcs.CommunicationComplexityTVDistanceExistsEventAbsMeasureRealSubEqHalfTotalVariation

/-!
# CommunicationComplexity.TVDistance.tvDistance_eq_tvDistanceSup

Topic: information   Node: 5f39b2be68bd

Provenance: helper lemma. TCSlib, `CommunicationComplexity.TVDistance.tvDistance_eq_tvDistanceSup`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equivalence of the two definitions of total variation distance. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$. Then the
total variation distance $\mathrm{TV}(\mu,\nu) =
\tfrac{1}{2}\norm{\mu-\nu}_{\mathrm{TV}}$, defined as half the total variation norm of
the signed measure $\mu-\nu$, agrees with its supremum form over events,
\[
\mathrm{TV}(\mu,\nu) \;=\; \sup\bigl\{\,\abs{\mu(S)-\nu(S)} : S \subseteq \Omega \text{
measurable}\,\bigr\}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open Classical in
/-- The total-variation-mass definition agrees with the supremum-over-events definition: `½ ‖μ − ν‖ = sup_S |μ(S) − ν(S)|` over measurable events `S`. [LPW17, §4.1, eq. (4.1) and Prop. 4.2] (LPW take the supremum as the definition and prove, in the finite case, that it is half the `ℓ¹` norm; here the identification goes through the Jordan/Hahn decomposition and holds on any measurable space). **Proof sketch.** Write `μ − ν = P − N` for the Jordan decomposition; then `P(Ω) = N(Ω)`, so half the total variation mass is `P(Ω)`. Step 1 (upper bound): for every event `S`, `|μ(S) − ν(S)| = |P(S) − N(S)| ≤ P(Ω)`, hence the supremum is at most `P(Ω)`. Step 2 (attained): the complement of a Hahn negative set carries all of `P` and none of `N`, so its gap is exactly `P(Ω)`; hence `P(Ω)` is at most the supremum. Conclude by antisymmetry. -/
theorem CommunicationComplexity.TVDistance.tvDistance_eq_tvDistanceSup
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDistance μ ν = tvDistanceSup μ ν := by
  let rhs : ℝ := (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ
  -- Step 1: every event gap is at most half the total variation mass
  have hset_le (S : {S : Set Ω // MeasurableSet S}) :
      |μ.real (S : Set Ω) - ν.real (S : Set Ω)| ≤ rhs := by
    simpa [rhs] using event_abs_measureReal_sub_le_half_totalVariation μ ν S
  have hrhs_nonneg : 0 ≤ rhs := by
    dsimp [rhs]
    positivity
  have hupper : tvDistanceSup μ ν ≤ rhs := by
    rw [tvDistanceSup]
    exact Real.sSup_le (by rintro _ ⟨S, rfl⟩; exact hset_le S) hrhs_nonneg
  -- Step 2: the Hahn-decomposition event attains it
  obtain ⟨Smax, hSmax⟩ := exists_event_abs_measureReal_sub_eq_half_totalVariation μ ν
  have hbdd :
      BddAbove (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |μ.real (S : Set Ω) - ν.real (S : Set Ω)|) := by
    exact ⟨rhs, by rintro _ ⟨S, rfl⟩; exact hset_le S⟩
  have hlower : rhs ≤ tvDistanceSup μ ν := by
    rw [tvDistanceSup]
    dsimp [rhs]
    rw [← hSmax]
    exact le_csSup hbdd (Set.mem_range_self Smax)
  rw [tvDistance]
  exact le_antisymm (by simpa [rhs] using hlower) (by simpa [rhs] using hupper)
