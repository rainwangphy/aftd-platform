import AFTD.Prelude

/-!
# CommunicationComplexity.FiniteMeasureSpace

Topic: communication   Node: 9e8cad380673

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.FiniteMeasureSpace`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 3 verbatim; compiled here.

A typeclass for a measurable space $\Omega$ that is simultaneously finite (carries a
\texttt{Fintype} instance) and discrete (every subset is measurable).  It deliberately
does not bundle a measure, so that a single type can be equipped with many different
measures.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
/-- A finite measurable space: the type is finite and the measurable structure is discrete. This deliberately does not include a measure. -/
class CommunicationComplexity.FiniteMeasureSpace (Ω : Type*) [MeasurableSpace Ω] where
  fintype :
    Fintype Ω
  discrete :
    DiscreteMeasurableSpace Ω

attribute [instance] CommunicationComplexity.FiniteMeasureSpace.fintype

attribute [instance] CommunicationComplexity.FiniteMeasureSpace.discrete
