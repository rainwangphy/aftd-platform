import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpace

/-!
# CommunicationComplexity.PublicCoin.newmanIndexSpace.fintype

Topic: communication   Node: d3864baed184

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.newmanIndexSpace.fintype`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Newman.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CommunicationComplexity.PublicCoin.newmanIndexSpace.fintype
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
noncomputable instance CommunicationComplexity.PublicCoin.newmanIndexSpace.fintype
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    Fintype (newmanIndexSpace X Y ε c) := inferInstance
