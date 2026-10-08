import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolOfProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol

/-!
# CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ofProtocol

Topic: communication   Node: 3e3dc1af1400

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ofProtocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Embeds a binary private-coin protocol into a private-coin finite-message protocol by
delegating to \texttt{Deterministic.FiniteMessage.Protocol.ofProtocol}.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω_X Ω_Y : Type*} {X Y α : Type*} in
/-- Embed a binary private-coin protocol into a finite-message protocol. Delegates to `Deterministic.FiniteMessage.Protocol.ofProtocol`. -/
abbrev CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ofProtocol (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.ofProtocol p
