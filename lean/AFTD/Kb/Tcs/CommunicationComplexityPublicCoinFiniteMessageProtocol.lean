import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol

Topic: communication   Node: 96d037aa8f70

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A public-coin finite-message protocol over shared-randomness space $\Omega$, private input
sets $X$ and $Y$, and output type $\alpha$ is a deterministic finite-message protocol in
which Alice's effective input is $\Omega \times X$ and Bob's effective input is
$\Omega \times Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- A public-coin finite-message protocol with randomness `Ω`, inputs `X`, `Y` and outputs `α`: a deterministic finite-message protocol where Alice's input is `Ω × X` and Bob's is `Ω × Y`, so both players see the shared random string [RY20, Ch. 3, §Variants of Randomized Protocols]. Deviation: each message is an element of an arbitrary finite type rather than a single bit, charged `⌈log₂ |β|⌉` bits. -/
abbrev CommunicationComplexity.PublicCoin.FiniteMessage.Protocol (Ω : Type*) (X Y α : Type*) :=
  Deterministic.FiniteMessage.Protocol (Ω × X) (Ω × Y) α
