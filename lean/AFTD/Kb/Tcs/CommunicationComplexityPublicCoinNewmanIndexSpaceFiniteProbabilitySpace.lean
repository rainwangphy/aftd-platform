import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceOf
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpace
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceBool
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceProd
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpacePi
import AFTD.Kb.Tcs.CommunicationComplexityInstProd
import AFTD.Kb.Tcs.CommunicationComplexityInstPi
import AFTD.Kb.Tcs.CommunicationComplexityUnitFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceFintype
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceNonempty
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceMeasureSpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceIsProbabilityMeasure

/-!
# CommunicationComplexity.PublicCoin.newmanIndexSpace.finiteProbabilitySpace

Topic: communication   Node: f81bd34764c1

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.newmanIndexSpace.finiteProbabilitySpace`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Newman.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CommunicationComplexity.PublicCoin.newmanIndexSpace.finiteProbabilitySpace
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
noncomputable instance CommunicationComplexity.PublicCoin.newmanIndexSpace.finiteProbabilitySpace
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    FiniteProbabilitySpace (newmanIndexSpace X Y ε c) :=
  FiniteProbabilitySpace.of (newmanIndexSpace X Y ε c)
