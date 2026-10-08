import AFTD.Prelude

/-!
# CommunicationComplexity.tvDistanceSup

Topic: information   Node: 1ae2fec0b9bd

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.tvDistanceSup`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{supremum definition} of total variation distance between $\mu$ and $\nu$ is
\[
  \mathrm{TV}_{\sup}(\mu,\nu)
  \;=\; \sup\bigl\{|\mu(S) - \nu(S)| : S \subseteq \Omega \text{ measurable}\bigr\}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- Total variation distance between probability measures, defined as the supremum over measurable events `S` of `|μ(S) − ν(S)|`. [LPW17, §4.1, eq. (4.1)] (statistical distance; also the `|p − q|` of [RY20, Lemma 6.6]). -/
noncomputable def CommunicationComplexity.tvDistanceSup {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  sSup (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
    |μ.real (S : Set Ω) - ν.real (S : Set Ω)|)
