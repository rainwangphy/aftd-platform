import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeMeasure

/-!
# CommunicationComplexity.coinTapeIsProbabilityMeasure

Topic: communication   Node: cfbe5e42c039

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.coinTapeIsProbabilityMeasure`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/CoinTape.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CommunicationComplexity.coinTapeIsProbabilityMeasure
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
noncomputable instance CommunicationComplexity.coinTapeIsProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (volume : Measure (CoinTape n)) := by
  change IsProbabilityMeasure (uniformOn Set.univ)
  exact uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty
