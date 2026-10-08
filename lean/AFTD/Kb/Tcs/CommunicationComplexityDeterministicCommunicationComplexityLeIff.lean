import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityInternalEnatIInfLeCoeIff

/-!
# CommunicationComplexity.Deterministic.communicationComplexity_le_iff

Topic: communication   Node: 00386fa1daf2

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.communicationComplexity_le_iff`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetComplexity.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Threshold characterization of deterministic communication complexity. Let $f : X \to Y \to \alpha$ be a two-argument function and let $n$ be a natural number.
Then the deterministic communication complexity $D(f)$ satisfies $D(f) \le n$ if and
only if there exists a deterministic communication protocol $p$ over inputs $X$ and $Y$
that computes $f$ and whose communication complexity is at most $n$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The deterministic communication complexity of `f` is at most `n` if and only if some protocol computes `f` using at most `n` bits. -/
theorem CommunicationComplexity.Deterministic.communicationComplexity_le_iff
    {X Y α : Type*} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : Protocol X Y α,
        p.Computes f ∧ p.complexity ≤ n := by
  simp only [communicationComplexity,
    Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]
