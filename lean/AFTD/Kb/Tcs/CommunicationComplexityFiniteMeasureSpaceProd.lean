import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceOf
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceBool

/-!
# CommunicationComplexity.finiteMeasureSpaceProd

Topic: communication   Node: c0114ec21745

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.finiteMeasureSpaceProd`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CommunicationComplexity.finiteMeasureSpaceProd
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
noncomputable instance CommunicationComplexity.finiteMeasureSpaceProd
    (Ω₁ Ω₂ : Type*) [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [FiniteMeasureSpace Ω₁] [FiniteMeasureSpace Ω₂] :
    FiniteMeasureSpace (Ω₁ × Ω₂) :=
  FiniteMeasureSpace.of (Ω₁ × Ω₂)
