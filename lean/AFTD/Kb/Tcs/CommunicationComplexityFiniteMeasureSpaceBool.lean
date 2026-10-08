import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceOf

/-!
# CommunicationComplexity.finiteMeasureSpaceBool

Topic: communication   Node: 5c88277fc1af

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.finiteMeasureSpaceBool`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CommunicationComplexity.finiteMeasureSpaceBool
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
instance CommunicationComplexity.finiteMeasureSpaceBool : FiniteMeasureSpace Bool :=
  FiniteMeasureSpace.of Bool
