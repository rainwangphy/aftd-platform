import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolCost
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicLeCommunicationComplexityIff

/-!
# CommunicationComplexity.Deterministic.OneWay.le_communicationComplexity_iff

Topic: communication   Node: 9ecf48792421

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.OneWay.le_communicationComplexity_iff`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lower bound characterization of one-way communication complexity. Let $f : X \to Y \to \alpha$ be a function and let $k \in \bbn$. Then $k$ is at most the
one-way deterministic communication complexity of $f$ (as an inequality in
$\bbn_\infty$) if and only if every one-way deterministic protocol that computes $f$ has
bit cost at least $k$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- The one-way communication complexity of `f` is at least `k` if and only if every one-way protocol computing `f` has cost at least `k`. -/
theorem CommunicationComplexity.Deterministic.OneWay.le_communicationComplexity_iff (f : X → Y → α) (k : ℕ) :
    (k : ENat) ≤ communicationComplexity f ↔
      ∀ p : Protocol X Y α, Protocol.Computes p f → k ≤ Protocol.cost p := by
  simp [communicationComplexity, le_iInf_iff, Nat.cast_le]
