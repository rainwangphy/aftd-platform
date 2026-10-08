import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexityLeIff
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesIsMonoPartition
import AFTD.Kb.Tcs.CommunicationComplexityRectangleFoolingSetNcardLeOfMonoPartition
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonoPartition
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsFoolingSet
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesFinite
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesCard
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComputes

/-!
# CommunicationComplexity.Deterministic.foolingSet_ncard_le_pow_of_communicationComplexity_le

Topic: communication   Node: a2e94593738e

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.foolingSet_ncard_le_pow_of_communicationComplexity_le`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Fooling set bound from communication complexity. Let $g : X \times Y \to \alpha$ be a two-argument function, and let $S \subseteq X
\times Y$ be a fooling set for $g$, meaning that $S$ meets every $g$-monochromatic
rectangle in at most one point. If the deterministic communication complexity of $g$
satisfies $D(g) \le n$ for some $n \in \bbn$, then the cardinality of $S$ satisfies
$\abs{S} \le 2^{n}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
open CommunicationComplexity.Rectangle in
/-- If the deterministic communication complexity of `g` is at most `n`, then every fooling set for `g` has at most `2 ^ n` elements [Rou16, Cor 4.7] (also [RY20, Ch. 1, §Using Fooling Sets]). Deviation: this is the exponential form of the fooling-set bound `⌈log₂ |S|⌉ ≤ D(g)`; `clog_ncard_le_communicationComplexity` restates it with `Nat.clog`. The proof combines the leaf-rectangle partition of a protocol of complexity at most `n` with the fact that a fooling set meets each monochromatic rectangle in at most one point. -/
theorem CommunicationComplexity.Deterministic.foolingSet_ncard_le_pow_of_communicationComplexity_le
    (g : X → Y → α) (S : Set (X × Y)) (n : ℕ)
    (hS : Rectangle.IsFoolingSet S g)
    (h : communicationComplexity g ≤ n) :
    Set.ncard S ≤ 2 ^ n := by
  obtain ⟨p, hp, hc⟩ := (communicationComplexity_le_iff g n).mp h
  let Part := Protocol.leafRectangles p
  have hPart : Rectangle.IsMonoPartition Part g :=
    Protocol.leafRectangles_isMonoPartition p g hp
  have hCard : Set.ncard Part ≤ 2 ^ n :=
    (Protocol.leafRectangles_card p).trans (Nat.pow_le_pow_right (by omega) hc)
  exact (Rectangle.foolingSet_ncard_le_of_monoPartition hS hPart
    (Protocol.leafRectangles_finite p)).trans hCard
