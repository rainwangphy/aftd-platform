import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonoPartition

/-!
# CommunicationComplexity.Rectangle.monoPartition_values_eq

Topic: communication   Node: 5a7915d22c1c

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Rectangle.monoPartition_values_eq`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Constant values within a part. Let $\mathcal{P}$ be a monochromatic rectangle partition for a function $g : X \to Y \to
\alpha$, and let $R \in \mathcal{P}$. Then $g$ is constant on $R$: for any $(x,y),
(x',y') \in R$ we have $g\,x\,y = g\,x'\,y'$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
variable {Part : Set (Set (X × Y))} {g : X → Y → α} in
/-- In a monochromatic rectangle partition, any two points in the same part have equal function values. -/
theorem CommunicationComplexity.Rectangle.monoPartition_values_eq (h : IsMonoPartition Part g)
    {R : Set (X × Y)} (hR : R ∈ Part)
    {x x' : X} {y y' : Y}
    (hxy : (x, y) ∈ R) (hx'y' : (x', y') ∈ R) :
    g x y = g x' y' :=
  h.2.1 R hR x x' y y' hxy hx'y'
