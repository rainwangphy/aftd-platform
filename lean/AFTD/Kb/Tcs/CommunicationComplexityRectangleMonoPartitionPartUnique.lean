import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonoPartition

/-!
# CommunicationComplexity.Rectangle.monoPartition_part_unique

Topic: communication   Node: 295351961ba7

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Rectangle.monoPartition_part_unique`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Uniqueness of the part containing a point. Let $\mathcal{P}$ be a monochromatic rectangle partition for a function $g : X \to Y \to
\alpha$, and let $R, S \in \mathcal{P}$. If some point $p \in X \times Y$ lies in both
$R$ and $S$, then $R = S$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
variable {Part : Set (Set (X × Y))} {g : X → Y → α} in
/-- If a point lies in two members of a monochromatic rectangle partition, the two members are equal. -/
theorem CommunicationComplexity.Rectangle.monoPartition_part_unique (h : IsMonoPartition Part g)
    {R S : Set (X × Y)} (hR : R ∈ Part) (hS : S ∈ Part)
    {p : X × Y} (hp1 : p ∈ R) (hp2 : p ∈ S) : R = S := by
  by_contra hne
  exact Set.disjoint_left.mp (h.2.2.2 R S hR hS hne) hp1 hp2
