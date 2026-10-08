import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolOfProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolOfProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrun

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol_rrun

Topic: communication   Node: 4e63150b173a

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol_rrun`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Embedding preserves randomized execution. Let $\Omega$ be a shared-randomness space, let $X$ and $Y$ be the private input sets of
the two players, and let $\alpha$ be an output type. Let $p$ be a binary public-coin
protocol over these types, that is, a deterministic protocol whose players receive
inputs in $\Omega \times X$ and $\Omega \times Y$. Embedding $p$ into the finite-message
framework—by treating each Boolean message as a message drawn from the two-element
type—and then running the result yields the same output as running $p$ directly: for
every private input $x \in X$, every private input $y \in Y$, and every shared random
string $\omega \in \Omega$, the finite-message embedding of $p$, executed on the paired
inputs $(\omega, x)$ and $(\omega, y)$, returns the same value in $\alpha$ as $p$
executed on those same paired inputs.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω : Type*} {X Y α : Type*} in
/-- The finite-message protocol obtained from a binary public-coin protocol `p` by `ofProtocol` has the same output as `p` on every input `x`, `y` and every random string `ω`. -/
@[simp]
theorem CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.ofProtocol_rrun
    (p : PublicCoin.Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    (ofProtocol p).rrun x y ω = p.rrun x y ω := by
  simp [rrun, PublicCoin.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.ofProtocol_run]
