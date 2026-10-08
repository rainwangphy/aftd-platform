import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexityLeOfFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolExists

/-!
# CommunicationComplexity.Deterministic.communicationComplexity_le_clog_card_X_alpha

Topic: communication   Node: 1a298b6bec0c

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.communicationComplexity_le_clog_card_X_alpha`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/UpperBounds.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Trivial upper bound on deterministic communication complexity. Let $X$ and $\alpha$ be finite nonempty types, let $Y$ be an arbitrary type, and let $f
: X \to Y \to \alpha$ be a two-argument function. Then the deterministic communication
complexity of $f$ satisfies
\[
  D(f) \;\le\; \lceil \log_2 \abs{X} \rceil + \lceil \log_2 \abs{\alpha} \rceil,
\]
where $\abs{X}$ and $\abs{\alpha}$ denote the cardinalities of $X$ and $\alpha$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The deterministic communication complexity of `f` is at most `⌈log₂ |X|⌉ + ⌈log₂ |α|⌉`, achieved by Alice sending her input, then Bob computing and sending the output [RY20, Ch. 1, §Equality: 'Alice sending her input yields an (n+1)-bit protocol'], [Rou16, §1.7]. Deviation: [RY20] only states the trivial protocol for specific functions (equality, disjointness); here it is stated for an arbitrary function with finite `X` and `α`. -/
theorem CommunicationComplexity.Deterministic.communicationComplexity_le_clog_card_X_alpha
    {X Y α : Type} [Finite X] [Finite α] [Nonempty X] [Nonempty α]
    (f : X → Y → α) :
    communicationComplexity f ≤
      Nat.clog 2 (Nat.card X) + Nat.clog 2 (Nat.card α) := by
  haveI := Fintype.ofFinite X; haveI := Fintype.ofFinite α
  exact communicationComplexity_le_of_finiteMessage_protocol
    (FiniteMessage.Protocol.alice id fun x =>
      FiniteMessage.Protocol.bob (f x) fun a =>
        FiniteMessage.Protocol.output a)
    -- Step 1: the protocol computes `f`
    (by ext x y; unfold FiniteMessage.Protocol.run; rfl)
    -- Step 2: its complexity is the claimed bound
    (by simp [FiniteMessage.Protocol.complexity, Nat.card_eq_fintype_card, Finset.sup_const])
