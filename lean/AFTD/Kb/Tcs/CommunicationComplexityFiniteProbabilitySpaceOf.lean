import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpaceOf
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.FiniteProbabilitySpace.of

Topic: communication   Node: b0df1ca43644

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.FiniteProbabilitySpace.of`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a type $\Omega$ already equipped with a \texttt{MeasureSpace}, \texttt{Fintype},
\texttt{DiscreteMeasurableSpace}, and \texttt{IsProbabilityMeasure} instance for
\texttt{volume}, this helper packages all of those into a \texttt{CommunicationComplexity.FiniteProbabilitySpace}
record.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
/-- The `FiniteProbabilitySpace` structure on a type `Ω` that already carries a `MeasureSpace`, `Fintype`, `DiscreteMeasurableSpace` and `IsProbabilityMeasure volume` instance, assembled from those instances. -/
noncomputable def CommunicationComplexity.FiniteProbabilitySpace.of
    (Ω : Type*)
    [m : MeasureSpace Ω]
    [Fintype Ω]
    [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] :
    FiniteProbabilitySpace Ω :=
{ toMeasureSpace := m
  finite := FiniteMeasureSpace.of Ω
  prob := inferInstance }
