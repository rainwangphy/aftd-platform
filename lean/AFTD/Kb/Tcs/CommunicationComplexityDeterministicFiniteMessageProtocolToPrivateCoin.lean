import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin

Topic: communication   Node: 34bddcea5f15

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a deterministic finite-message protocol $p$, the operation
\texttt{CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin} converts it into a
private-coin finite-message protocol over arbitrary coin spaces $\Omega_X$ and
$\Omega_Y$ by ignoring both coin inputs (via \texttt{comap} with $\mathrm{Prod.snd}$).
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- Convert a deterministic finite-message protocol to a private-coin finite-message protocol by ignoring both coin spaces (via comap). -/
abbrev CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toPrivateCoin
    {X Y α Ω_X Ω_Y : Type*}
    (p : Deterministic.FiniteMessage.Protocol X Y α) :
    PrivateCoin.FiniteMessage.Protocol Ω_X Ω_Y X Y α :=
  p.comap Prod.snd Prod.snd
