import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol

/-!
# CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

Topic: communication   Node: a983a7632213

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A private-coin finite-message protocol over input types $X$, $Y$ with private
randomness types $\Omega_X$, $\Omega_Y$ and output type $\alpha$ is defined as a
deterministic finite-message protocol whose effective input for Alice is
$\Omega_X \times X$ and for Bob is $\Omega_Y \times Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- A private-coin finite-message protocol with randomness `Ω_X` for Alice and `Ω_Y` for Bob, inputs `X`, `Y` and outputs `α`: a deterministic finite-message protocol where Alice's input is `Ω_X × X` and Bob's is `Ω_Y × Y`, so each player sees only their own random string [RY20, Ch. 3, §Variants of Randomized Protocols]. Deviation: each message is an element of an arbitrary finite type rather than a single bit, charged `⌈log₂ |β|⌉` bits. -/
abbrev CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol (Ω_X Ω_Y : Type*) (X Y α : Type*) :=
  Deterministic.FiniteMessage.Protocol (Ω_X × X) (Ω_Y × Y) α
