import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToCoinTapeApproxSatisfies
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToCoinTapeComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinCommunicationComplexityLeIffFiniteMessage
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolApproxComputesEqApproxSatisfies
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
import AFTD.Kb.Tcs.CommunicationComplexityInstProd
import AFTD.Kb.Tcs.CommunicationComplexityInstPi
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolApproxSatisfies
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape

/-!
# CommunicationComplexity.PrivateCoin.communicationComplexity_le_of_finiteMessage

Topic: communication   Node: 1ef23b95dfd4

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PrivateCoin.communicationComplexity_le_of_finiteMessage`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComplexity.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finite-probability protocols bound private-coin complexity. Let $X$, $Y$, and $\alpha$ be types, let $f : X \to Y \to \alpha$ be the function to be
computed, and let $\Omega_X$ and $\Omega_Y$ be finite probability spaces serving as the
two players' private randomness. Fix real numbers $\varepsilon'$ and $\varepsilon$ with
$\varepsilon' < \varepsilon$, and let $p$ be a finite-message private-coin protocol with
randomness spaces $\Omega_X$ and $\Omega_Y$, input types $X$ and $Y$, and output type
$\alpha$, and suppose that $p$ computes $f$ with error at most $\varepsilon'$, i.e.\ for
every input pair $(x,y)$ the probability that $p$ returns a value other than $f(x,y)$ is
at most $\varepsilon'$. Then the $\varepsilon$-error private-coin randomized
communication complexity of $f$ satisfies $R_\varepsilon(f) \le \mathrm{complexity}(p)$,
where the right-hand side is the worst-case number of bits exchanged by $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- If a private-coin finite-message protocol over arbitrary finite probability spaces `ε'`-computes `f` with `ε' < ε`, then the private-coin communication complexity at error `ε` is at most the protocol's complexity. The strict inequality pays for replacing the two given probability spaces by coin tapes via `toCoinTape`, which approximates the distributions to within the slack `ε - ε'` at no cost in communication. -/
theorem CommunicationComplexity.PrivateCoin.communicationComplexity_le_of_finiteMessage
    {X Y α} {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    (f : X → Y → α) (ε ε' : ℝ) (hε : ε' < ε)
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (hp : p.ApproxComputes f ε') :
    PrivateCoin.communicationComplexity f ε ≤ p.complexity := by
  rw [communicationComplexity_le_iff_finiteMessage]
  -- Convert ApproxComputes to ApproxSatisfies
  rw [FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies] at hp
  -- Use toCoinTape to get a CoinTape-based protocol
  have hδ : 0 < ε - ε' := sub_pos.mpr hε
  let tc := p.toCoinTape (ε - ε') hδ
  refine ⟨tc.1, tc.2.1, tc.2.2, ?_, le_of_eq ?_⟩
  · -- ApproxComputes at error ε
    rw [FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies]
    -- toCoinTape_approxSatisfies gives error ε' + (ε - ε') = ε
    have h := p.toCoinTape_approxSatisfies _ ε' (ε - ε') hδ hp
    convert h using 1; ring
  · exact p.toCoinTape_complexity (ε - ε') hδ
