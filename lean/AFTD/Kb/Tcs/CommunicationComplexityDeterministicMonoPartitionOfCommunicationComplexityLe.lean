import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexityLeIff
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesIsMonoPartition
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonoPartition
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesCard
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComputes

/-!
# CommunicationComplexity.Deterministic.mono_partition_of_communicationComplexity_le

Topic: communication   Node: e41818c9c51d

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.mono_partition_of_communicationComplexity_le`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Low deterministic complexity yields a small monochromatic partition. Let $g : X \times Y \to \alpha$ be a two-argument function, and let $n$ be a natural
number. If the deterministic communication complexity $D(g)$ satisfies $D(g) \le n$,
then there is a collection $\mathcal{P}$ of subsets of $X \times Y$ that is a
monochromatic rectangle partition for $g$ — every member is a rectangle, every member is
monochromatic for $g$, the members cover $X \times Y$, and distinct members are disjoint
— and whose number of parts satisfies $\abs{\mathcal{P}} \le 2^n$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- If the deterministic communication complexity of `g` is at most `n`, then there is a monochromatic rectangle partition of `X × Y` for `g` with at most `2 ^ n` rectangles [RY20, Thm 1.7]: take the leaf rectangles of a protocol of complexity at most `n`. -/
theorem CommunicationComplexity.Deterministic.mono_partition_of_communicationComplexity_le
    (g : X → Y → α) (n : ℕ)
    (h : communicationComplexity g ≤ n) :
    ∃ Part : Set (Set (X × Y)),
      Rectangle.IsMonoPartition Part g ∧
      Set.ncard Part ≤ 2 ^ n := by
  obtain ⟨p, hp, hc⟩ := (communicationComplexity_le_iff g n).mp h
  exact ⟨Protocol.leafRectangles p,
    Protocol.leafRectangles_isMonoPartition p g hp,
    (Protocol.leafRectangles_card p).trans
      (Nat.pow_le_pow_right (by omega) hc)⟩
