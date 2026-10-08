import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toDeterministic

Topic: communication   Node: ea967345706d

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toDeterministic`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a public-coin finite-message protocol $p$ and a fixed randomness sample
$\omega : \Omega$, \texttt{PublicCoin.FiniteMessage.Protocol.toDeterministic}~$p~\omega$
is the deterministic finite-message protocol obtained by substituting $\omega$
for the shared randomness (via \texttt{comap} with $\mathrm{Prod.mk}\,\omega$).
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- Fix the randomness of a public-coin finite-message protocol, producing a deterministic finite-message protocol with the same complexity (via comap). -/
abbrev CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toDeterministic
    {Ω X Y α : Type*}
    (p : PublicCoin.FiniteMessage.Protocol Ω X Y α) (ω : Ω) :
    Deterministic.FiniteMessage.Protocol X Y α :=
  p.comap (Prod.mk ω) (Prod.mk ω)
