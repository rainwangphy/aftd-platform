import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceOf
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceBool
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceProd
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpacePi
import AFTD.Kb.Tcs.CommunicationComplexityInstProd
import AFTD.Kb.Tcs.CommunicationComplexityInstPi
import AFTD.Kb.Tcs.CommunicationComplexityUnitMeasureSpace

/-!
# CommunicationComplexity.Unit.finiteProbabilitySpace

Topic: communication   Node: c76f4c3d7983

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Unit.finiteProbabilitySpace`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Newman.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

CommunicationComplexity.Unit.finiteProbabilitySpace
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
noncomputable instance CommunicationComplexity.Unit.finiteProbabilitySpace :
    FiniteProbabilitySpace Unit :=
  haveI : IsProbabilityMeasure (volume : Measure Unit) := Measure.dirac.isProbabilityMeasure
  FiniteProbabilitySpace.of Unit
