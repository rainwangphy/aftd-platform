import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolOfProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol

Topic: communication   Node: 1375cbff5cbd

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Embeds a binary public-coin protocol into a finite-message protocol by delegating to
\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol}.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω : Type*} {X Y α : Type*} in
/-- Embed a binary public-coin protocol into a finite-message protocol. Delegates to `Deterministic.FiniteMessage.Protocol.ofProtocol`. -/
abbrev CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol (p : PublicCoin.Protocol Ω X Y α) :
    Protocol Ω X Y α :=
  Deterministic.FiniteMessage.Protocol.ofProtocol p
