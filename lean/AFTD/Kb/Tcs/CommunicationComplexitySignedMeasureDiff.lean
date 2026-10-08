import AFTD.Prelude

/-!
# CommunicationComplexity.signedMeasureDiff

Topic: information   Node: d1e58a081db6

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.signedMeasureDiff`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given two probability measures $\mu$ and $\nu$ on a measurable space $\Omega$, the
\emph{signed measure difference} $\mu - \nu$ is the signed measure on $\Omega$ obtained
by taking the difference of $\mu$ and $\nu$ as measures.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- The signed difference between two probability measures, represented as measures with `IsProbabilityMeasure` instances. -/
noncomputable def CommunicationComplexity.signedMeasureDiff {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : SignedMeasure Ω :=
  μ.toSignedMeasure - ν.toSignedMeasure
