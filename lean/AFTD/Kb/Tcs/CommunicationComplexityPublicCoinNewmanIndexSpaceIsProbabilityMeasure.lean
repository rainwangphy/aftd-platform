import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceFintype
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceNonempty
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceMeasureSpace

/-!
# CommunicationComplexity.PublicCoin.newmanIndexSpace.isProbabilityMeasure

Topic: communication   Node: 8b9b60b1491f

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.newmanIndexSpace.isProbabilityMeasure`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Newman.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CommunicationComplexity.PublicCoin.newmanIndexSpace.isProbabilityMeasure
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
noncomputable instance CommunicationComplexity.PublicCoin.newmanIndexSpace.isProbabilityMeasure
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    IsProbabilityMeasure (volume : Measure (newmanIndexSpace X Y ε c)) := by
  change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
  infer_instance
