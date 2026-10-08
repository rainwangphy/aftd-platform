import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolApproxComputes
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
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolOfProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolOfProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeIsProbabilityMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolApproxComputes

/-!
# CommunicationComplexity.PrivateCoin.communicationComplexity

Topic: communication   Node: 8a22eac9068f

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PrivateCoin.communicationComplexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComplexity.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The $\varepsilon$-error private-coin randomized communication complexity of $f : X \to Y \to \alpha$
is the extended natural number
\[
  R_\varepsilon(f)
  \;=\;
  \inf_{\substack{n_X, n_Y \in \mathbb{N},\\ p : \mathrm{Protocol}(\{0,1\}^{n_X}, \{0,1\}^{n_Y}, X, Y, \alpha),\\ p.\mathrm{ApproxComputes}\,f\,\varepsilon}} p.\mathrm{complexity},
\]
i.e.\ the minimum worst-case number of bits exchanged over all private-coin randomized
protocols that compute $f$ with error at most $\varepsilon$ on every input.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- The `ε`-error private-coin randomized communication complexity `R^priv_ε(f)` of `f`, defined as the minimum worst-case number of bits exchanged over all private-coin randomized protocols that compute `f` with error at most `ε` on every input [RY20, Ch. 3, §Variants of Randomized Protocols]. Deviation: the minimum is an infimum in `ℕ∞` (equal to `⊤` if no protocol qualifies), and the two players' private randomness are coin tapes `CoinTape nX` and `CoinTape nY` of some finite lengths, quantified over all `nX`, `nY`. -/
noncomputable def CommunicationComplexity.PrivateCoin.communicationComplexity
    {X Y α} (f : X → Y → α) (ε : ℝ) : ENat :=
  ⨅ (nX : ℕ) (nY : ℕ)
    (p : Protocol (CoinTape nX) (CoinTape nY) X Y α)
    (_ : p.ApproxComputes f ε),
    (p.complexity : ENat)
