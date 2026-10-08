import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonoPartition
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangleIff

/-!
# CommunicationComplexity.Rectangle.monoPartition_cross_mem

Topic: communication   Node: a3fb3f198556

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Rectangle.monoPartition_cross_mem`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cross closure within a part. Let $\mathcal{P}$ be a monochromatic rectangle partition for a function $g : X \to Y \to
\alpha$, and let $R \in \mathcal{P}$. If $(x,y)$ and $(x',y')$ both belong to $R$, then
the two "crossed" pairs $(x',y)$ and $(x,y')$ also belong to $R$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
variable {Part : Set (Set (X × Y))} {g : X → Y → α} in
/-- In a monochromatic rectangle partition, if `(x,y)` and `(x',y')` are in the same part, then so are `(x',y)` and `(x,y')`. -/
theorem CommunicationComplexity.Rectangle.monoPartition_cross_mem (h : IsMonoPartition Part g)
    {R : Set (X × Y)} (hR : R ∈ Part)
    {x x' : X} {y y' : Y}
    (hxy : (x, y) ∈ R) (hx'y' : (x', y') ∈ R) :
    (x', y) ∈ R ∧ (x, y') ∈ R :=
  (IsRectangle_iff R).mp (h.1 R hR) x x' y y' hxy hx'y'
