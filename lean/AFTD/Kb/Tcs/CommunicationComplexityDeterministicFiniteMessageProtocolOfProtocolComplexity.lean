import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolOfProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolClogTwoTwo

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_complexity

Topic: communication   Node: 631e41b5f1e8

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Embedding binary protocols preserves complexity. Let $p$ be a deterministic binary two-party communication protocol over input types $X$
and $Y$ with output type $\alpha$, and let its embedding into the finite-message
framework send each Boolean message as an element of $\{\mathtt{false},\mathtt{true}\}$.
Then the communication complexity of the embedded finite-message protocol equals the
communication complexity of $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Viewing a binary protocol as a finite-message protocol does not change its complexity: each `Bool`-valued message costs `⌈log₂ 2⌉ = 1` bit. -/
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_complexity (p : Deterministic.Protocol X Y α) :
    (ofProtocol p).complexity = p.complexity := by
  induction p <;> simp only [ofProtocol, complexity,
    Deterministic.Protocol.complexity, Fintype.univ_bool,
    Finset.sup_insert, Finset.sup_singleton,
    Fintype.card_bool, clog_two_two,
    Nat.max_comm, *]
