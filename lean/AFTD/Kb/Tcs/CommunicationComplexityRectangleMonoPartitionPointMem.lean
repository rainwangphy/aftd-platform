import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonoPartition

/-!
# CommunicationComplexity.Rectangle.monoPartition_point_mem

Topic: communication   Node: 5dd808a23584

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Rectangle.monoPartition_point_mem`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every point lies in some part of a partition. Let $g : X \times Y \to \alpha$ and let $\mathcal{P}$ be a monochromatic rectangle
partition for $g$. Then every point $p \in X \times Y$ belongs to at least one member $R
\in \mathcal{P}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
variable {Part : Set (Set (X × Y))} {g : X → Y → α} in
/-- Every point of `X × Y` lies in some member of a monochromatic rectangle partition. -/
theorem CommunicationComplexity.Rectangle.monoPartition_point_mem (h : IsMonoPartition Part g)
    (p : X × Y) : ∃ R ∈ Part, p ∈ R := by
  have := h.2.2.1 ▸ Set.mem_univ p
  exact Set.mem_sUnion.mp this
