import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexitySignedMeasureDiff

/-!
# CommunicationComplexity.tvDistance

Topic: information   Node: 8d0bdad41500

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.tvDistance`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{total variation distance} between two probability measures $\mu$ and $\nu$ on
$\Omega$ is defined as $\tfrac{1}{2}$ times the total variation norm of the signed
measure $\mu - \nu$, i.e.\
$\mathrm{TV}(\mu,\nu) = \tfrac{1}{2}\|\mu - \nu\|_{\mathrm{TV}}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- Total variation distance between probability measures, defined as half the total mass of the total variation `|μ − ν|` of the signed measure `μ - ν` (i.e. half of `P(Ω) + N(Ω)` for the Jordan decomposition `μ − ν = P − N`). [LPW17, §4.1, eq. (4.1)] (statistical distance; also the `|p − q|` of [RY20, Lemma 6.6]); deviation: LPW define it as the supremum over events (`tvDistanceSup` here) and prove the other forms; `tvDistance_eq_tvDistanceSup` shows the two agree. -/
noncomputable def CommunicationComplexity.tvDistance {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ
