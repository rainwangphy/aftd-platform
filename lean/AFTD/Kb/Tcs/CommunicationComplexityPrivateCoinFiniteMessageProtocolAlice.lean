import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol

/-!
# CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.alice

Topic: communication   Node: d376317d3def

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.alice`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a function $f : X \to \Omega_X \to \beta$ (Alice's message function depending on
her public input and private randomness) and a continuation $P : \beta \to
\mathsf{Protocol}$, constructs a protocol node at which Alice sends a $\beta$-valued
message and execution branches on it.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω_X Ω_Y : Type*} {X Y α : Type*} in
/-- Alice sends a `β`-valued message depending on her input `x` and private randomness `ω_x`. -/
def CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.alice {β : Type} [Fintype β] [Nonempty β]
    (f : X → Ω_X → β) (P : β → Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.alice (fun ⟨ω, x⟩ => f x ω) P
