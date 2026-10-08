import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol

/-!
# CommunicationComplexity.PrivateCoin.Protocol

Topic: communication   Node: fb4a899bcf2a

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PrivateCoin.Protocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A \emph{private-coin protocol} with randomness spaces $\Omega_X$ and $\Omega_Y$, input
spaces $X$ and $Y$, and output type $\alpha$ is defined as a deterministic protocol
$\texttt{Deterministic.Protocol}\;(\Omega_X \times X)\;(\Omega_Y \times Y)\;\alpha$.
Alice's message function receives the pair $(\omega_x, x)$ and Bob's receives
$(\omega_y, y)$, so each player's coin flip is invisible to the other.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- A private-coin protocol with randomness `Ω_X` for Alice and `Ω_Y` for Bob, inputs `X`, `Y` and outputs `α`: a deterministic protocol where Alice's input is augmented with her private randomness and Bob's with his, so Alice's message functions see `(ω_x, x)` and Bob's see `(ω_y, y)`, and neither player sees the other's coins [RY20, Ch. 3, §Variants of Randomized Protocols: private coins]. -/
abbrev CommunicationComplexity.PrivateCoin.Protocol (Ω_X Ω_Y : Type*) (X Y α : Type*) :=
  Deterministic.Protocol (Ω_X × X) (Ω_Y × Y) α
