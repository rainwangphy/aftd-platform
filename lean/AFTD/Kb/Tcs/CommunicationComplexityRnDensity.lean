import AFTD.Prelude

/-!
# CommunicationComplexity.rnDensity

Topic: information   Node: 2326a7a3a428

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.rnDensity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For two probability measures $\mu$ and $\nu$ on a measurable space $\Omega$, the
\emph{Radon-Nikodym density} $\mathrm{rnDensity}(\mu,\nu)(x) \in \mathbb{R}$ is
the real part of the Radon-Nikodym derivative $\frac{d\mu}{d\nu}(x)$, obtained by
converting the extended non-negative real value $\mu.\mathrm{rnDeriv}\,\nu\,x$
to a real number via \texttt{ENNReal.toReal}.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The real-valued Radon-Nikodym density `dμ/dν` (as a real number, via `toReal`) used in the absolutely-continuous part of Pinsker. -/
noncomputable def CommunicationComplexity.rnDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : Ω) : ℝ :=
  ((μ.rnDeriv ν x).toReal)
