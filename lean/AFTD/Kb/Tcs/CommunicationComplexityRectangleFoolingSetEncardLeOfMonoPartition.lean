import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsFoolingSet
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonoPartition
import AFTD.Kb.Tcs.CommunicationComplexityRectangleMonoPartitionPointMem

/-!
# CommunicationComplexity.Rectangle.foolingSet_encard_le_of_monoPartition

Topic: communication   Node: 17df121340a8

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Rectangle.foolingSet_encard_le_of_monoPartition`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fooling set bound from a monochromatic rectangle partition. Let $X$, $Y$, and $\alpha$ be sets and let $g : X \times Y \to \alpha$. If $S \subseteq
X \times Y$ is a fooling set for $g$ and $\mathcal{P}$ is a monochromatic rectangle
partition for $g$, then the cardinality of $S$ is at most the cardinality of
$\mathcal{P}$, that is $\abs{S} \le \abs{\mathcal{P}}$, where cardinalities are compared
as extended natural numbers (allowing the value $\infty$).
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
variable {Part : Set (Set (X × Y))} {g : X → Y → α} in
open Classical in
/-- Any monochromatic rectangle partition has at least as many parts as any fooling set for the same function (as extended cardinals, so no finiteness is assumed). [Rou16, Cor 4.7] (its proof: each fooling-set element needs its own monochromatic rectangle). Deviation: Rou16 conclude `D(g) ≥ log₂ |F|`; the statement here is the combinatorial core comparing `|F|` with the size of an arbitrary monochromatic rectangle partition, which yields Rou16's form once combined with the `2^c`-part partition of [RY20, Thm 1.7]. The proof chooses, for each point, a member containing it; on the fooling set this choice is injective because a member containing two fooling-set points would be a monochromatic rectangle meeting the fooling set twice. -/
theorem CommunicationComplexity.Rectangle.foolingSet_encard_le_of_monoPartition
    {S : Set (X × Y)} (hS : IsFoolingSet S g) (hPart : IsMonoPartition Part g) :
    S.encard ≤ Part.encard := by
  choose rect hrect_mem hrect_in using fun p : X × Y => monoPartition_point_mem hPart p
  have hmaps : ∀ p ∈ S, rect p ∈ Part := fun p _ => hrect_mem p
  have hinj : Set.InjOn rect S := by
    intro p hp q hq hpq
    have hsub :=
      hS (rect p) (hPart.1 _ (hrect_mem p)) (hPart.2.1 _ (hrect_mem p))
    exact hsub ⟨hp, hrect_in p⟩ ⟨hq, by simpa [hpq] using hrect_in q⟩
  exact Set.encard_le_encard_of_injOn hmaps hinj
