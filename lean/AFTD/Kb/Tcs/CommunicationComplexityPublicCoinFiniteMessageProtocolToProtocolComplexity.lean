import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toProtocol_complexity

Topic: communication   Node: a5329c58197f

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toProtocol_complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Conversion to a binary public-coin protocol preserves communication complexity. Let $\Omega$ be a shared-randomness space and let $p$ be a public-coin finite-message
protocol with Alice's private input in $X$, Bob's in $Y$, and output in $\alpha$; that
is, a deterministic finite-message protocol whose effective input types are $\Omega
\times X$ for Alice and $\Omega \times Y$ for Bob, in which each message is an element
of an arbitrary finite nonempty type $\beta$ costing $\lceil \log_2 \abs{\beta} \rceil$
bits. Then the binary public-coin protocol obtained from $p$ by encoding every
$\beta$-valued message as $\lceil \log_2 \abs{\beta} \rceil$ bits has communication
complexity exactly equal to that of $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω : Type*} {X Y α : Type*} in
/-- The binary public-coin protocol obtained from a finite-message protocol `p` by `toProtocol` has exactly the complexity of `p`, where a `β`-valued message of `p` is charged `⌈log₂ |β|⌉` bits. -/
@[simp]
theorem CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.toProtocol_complexity (p : Protocol Ω X Y α) :
    (p.toProtocol).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.toProtocol_complexity p
