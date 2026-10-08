import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsFoolingSet
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonoPartition
import AFTD.Kb.Tcs.CommunicationComplexityRectangleFoolingSetEncardLeOfMonoPartition

/-!
# CommunicationComplexity.Rectangle.foolingSet_ncard_le_of_monoPartition

Topic: communication   Node: 1104fa5e340a

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Rectangle.foolingSet_ncard_le_of_monoPartition`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fooling set bound via monochromatic partition. Let $g : X \times Y \to \alpha$, let $S \subseteq X \times Y$ be a fooling set for $g$,
and let $\mathcal{P}$ be a monochromatic rectangle partition for $g$. If $\mathcal{P}$
is finite, then the number of points of $S$ is at most the number of members of
$\mathcal{P}$; that is, $\abs{S} \le \abs{\mathcal{P}}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
variable {Part : Set (Set (X × Y))} {g : X → Y → α} in
/-- Any finite monochromatic rectangle partition has at least as many parts as any fooling set for the same function (as natural-number cardinalities; the fooling set is then finite too). [Rou16, Cor 4.7] (its proof: each fooling-set element needs its own monochromatic rectangle); see `foolingSet_encard_le_of_monoPartition` for the deviation. -/
theorem CommunicationComplexity.Rectangle.foolingSet_ncard_le_of_monoPartition
    {S : Set (X × Y)} (hS : IsFoolingSet S g) (hPart : IsMonoPartition Part g)
    (hfin : Part.Finite) :
    Set.ncard S ≤ Set.ncard Part := by
  have henc := foolingSet_encard_le_of_monoPartition hS hPart
  have hSfin : S.Finite := hfin.finite_of_encard_le henc
  simpa [Set.ncard] using ENat.toNat_le_toNat henc hfin.encard_lt_top.ne
