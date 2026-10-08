import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexityLeIff
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicLeCommunicationComplexityIff
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicMonoPartitionOfCommunicationComplexityLe
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonoPartition
import AFTD.Kb.Tcs.G

/-!
# CommunicationComplexity.Deterministic.le_communicationComplexity_of_forall_lt_ncard

Topic: communication   Node: f81e588bf78f

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.le_communicationComplexity_of_forall_lt_ncard`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Rectangle-partition lower bound on communication complexity. Let $g : X \to Y \to \alpha$ be a two-argument function and let $n$ be a natural number.
If every monochromatic rectangle partition of $g$ consists of strictly more than $2^n$
parts, then the deterministic communication complexity of $g$ satisfies $n + 1 \le
D(g)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Rectangle lower-bound method: if every monochromatic rectangle partition of `X × Y` for `g` has more than `2 ^ n` parts, then the deterministic communication complexity of `g` is at least `n + 1` [RY20, Thm 1.7] (contrapositive) / [Rou16, Thm 4.3]. Deviation: stated with `2 ^ n` parts and conclusion `n + 1 ≤ D(g)` rather than `log₂ t ≤ D(g)` for a partition size `t`, avoiding logarithms of naturals. -/
theorem CommunicationComplexity.Deterministic.le_communicationComplexity_of_forall_lt_ncard
    (g : X → Y → α) (n : ℕ)
    (h : ∀ Part : Set (Set (X × Y)),
      Rectangle.IsMonoPartition Part g →
      2 ^ n < Set.ncard Part) :
    (n + 1 : ℕ) ≤ communicationComplexity g := by
  rw [le_communicationComplexity_iff]
  intro p hp
  have hle : communicationComplexity g ≤
      p.complexity :=
    (communicationComplexity_le_iff g p.complexity).mpr ⟨p, hp, le_refl _⟩
  obtain ⟨Part, hPart, hCard⟩ :=
    mono_partition_of_communicationComplexity_le g p.complexity hle
  have hsuff := h Part hPart
  by_contra hlt; push_neg at hlt
  have : 2 ^ p.complexity ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega
