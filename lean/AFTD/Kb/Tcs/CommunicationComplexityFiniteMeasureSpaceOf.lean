import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpace

/-!
# CommunicationComplexity.FiniteMeasureSpace.of

Topic: communication   Node: 0be3a5486844

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.FiniteMeasureSpace.of`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a type $\Omega$ that already carries \texttt{Fintype} and
\texttt{DiscreteMeasurableSpace} instances, \texttt{CommunicationComplexity.FiniteMeasureSpace.of} bundles them
into a \texttt{FiniteMeasureSpace} record without requiring any additional data.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
/-- The `FiniteMeasureSpace` structure on a type `Ω` that already carries `Fintype` and `DiscreteMeasurableSpace` instances, assembled from those instances. -/
def CommunicationComplexity.FiniteMeasureSpace.of
    (Ω : Type*) [MeasurableSpace Ω] [Fintype Ω] [DiscreteMeasurableSpace Ω] :
    FiniteMeasureSpace Ω :=
{ fintype := inferInstance
  discrete := inferInstance }
