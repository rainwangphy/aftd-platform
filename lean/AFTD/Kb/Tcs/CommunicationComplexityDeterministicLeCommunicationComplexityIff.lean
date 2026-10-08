import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity

/-!
# CommunicationComplexity.Deterministic.le_communicationComplexity_iff

Topic: communication   Node: 17bb832b9158

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.le_communicationComplexity_iff`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetComplexity.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lower-bound characterization of communication complexity. Let $f : X \to Y \to \alpha$ be a two-argument function, let $D(f) \in \bbn_\infty$
denote its deterministic communication complexity, and let $n$ be a natural number. Then
$n \le D(f)$ if and only if every deterministic protocol $p$ that computes $f$ has
communication complexity at least $n$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The deterministic communication complexity of `f` is at least `n` if and only if every protocol computing `f` uses at least `n` bits. This is the form in which lower bounds are proved. -/
theorem CommunicationComplexity.Deterministic.le_communicationComplexity_iff
    {X Y α : Type*} (f : X → Y → α) (n : ℕ) :
    (n : ENat) ≤ communicationComplexity f ↔
      ∀ p : Protocol X Y α,
        p.Computes f → n ≤ p.complexity := by
  simp only [communicationComplexity,
    le_iInf_iff, Nat.cast_le]
