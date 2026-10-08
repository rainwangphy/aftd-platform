import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceOf
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceBool
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceProd

/-!
# CommunicationComplexity.finiteMeasureSpacePi

Topic: communication   Node: 616fb8a8d7d9

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.finiteMeasureSpacePi`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CommunicationComplexity.finiteMeasureSpacePi
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
open Classical in
noncomputable instance CommunicationComplexity.finiteMeasureSpacePi
    {ι : Type*} [Fintype ι] (Ω : ι → Type*) [∀ i, MeasurableSpace (Ω i)]
    [∀ i, FiniteMeasureSpace (Ω i)] :
    FiniteMeasureSpace ((i : ι) → Ω i) :=
  FiniteMeasureSpace.of ((i : ι) → Ω i)
