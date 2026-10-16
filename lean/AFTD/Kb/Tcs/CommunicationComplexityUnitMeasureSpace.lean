import AFTD.Prelude

/-!
# CommunicationComplexity.Unit.measureSpace

Topic: communication   Node: b444d8023bf5

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Unit.measureSpace`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Newman.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Unit with the Dirac probability measure.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- Unit with the Dirac probability measure. -/
noncomputable instance CommunicationComplexity.Unit.measureSpace : MeasureSpace Unit :=
  ⟨Measure.dirac ()⟩
