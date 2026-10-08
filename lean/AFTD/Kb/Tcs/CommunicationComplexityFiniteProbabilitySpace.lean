import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpace

/-!
# CommunicationComplexity.FiniteProbabilitySpace

Topic: communication   Node: cd502524e511

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.FiniteProbabilitySpace`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 4 verbatim; compiled here.

A typeclass bundling a \texttt{MeasureSpace} structure on $\Omega$ together with a
\texttt{CommunicationComplexity.FiniteMeasureSpace} witness and an \texttt{IsProbabilityMeasure} instance for the
canonical volume measure.  This makes $\Omega$ simultaneously a finite discrete
measurable space and a probability space.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
/-- A finite probability space: a type `Ω` equipped with a measure space structure whose measurable structure is discrete, whose underlying type is finite, and whose `volume` is a probability measure. This is the ambient structure for the randomness of public-coin and private-coin protocols. -/
class CommunicationComplexity.FiniteProbabilitySpace (Ω : Type*) where
  toMeasureSpace : MeasureSpace Ω
  finite :
    @FiniteMeasureSpace Ω toMeasureSpace.toMeasurableSpace
  prob :
    @IsProbabilityMeasure Ω
      toMeasureSpace.toMeasurableSpace toMeasureSpace.volume

attribute [instance] CommunicationComplexity.FiniteProbabilitySpace.toMeasureSpace

attribute [instance] CommunicationComplexity.FiniteProbabilitySpace.finite

attribute [instance] CommunicationComplexity.FiniteProbabilitySpace.prob
