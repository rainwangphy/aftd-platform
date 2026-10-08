import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolOfProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolOfProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToDeterministic

/-!
# CommunicationComplexity.PublicCoin.Protocol.toDeterministic

Topic: communication   Node: 9af1179607d7

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.Protocol.toDeterministic`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Comparison.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a public-coin protocol $p$ over randomness space $\Omega$ and a fixed
outcome $\omega : \Omega$, \texttt{PublicCoin.Protocol.toDeterministic}~$p~\omega$
is the deterministic protocol obtained by substituting $\omega$ for the shared
randomness (implemented via \texttt{comap} with $\mathrm{Prod.mk}\,\omega$).
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- Fix the randomness of a binary public-coin protocol, producing a deterministic protocol with the same complexity (via comap). -/
abbrev CommunicationComplexity.PublicCoin.Protocol.toDeterministic
    {Ω X Y α : Type*}
    (p : PublicCoin.Protocol Ω X Y α) (ω : Ω) :
    Deterministic.Protocol X Y α :=
  p.comap (Prod.mk ω) (Prod.mk ω)
