import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToPrivateCoinComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToDeterministicComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolDerandomizationSamples
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolNewmanProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpace
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolAlice
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToDeterministicRun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToCoinTapeComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToCoinTapeComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityInstProd
import AFTD.Kb.Tcs.CommunicationComplexityInstPi
import AFTD.Kb.Tcs.CommunicationComplexityUnitFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceFintype
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceNonempty
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceMeasureSpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceIsProbabilityMeasure
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToPrivateCoin
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToDeterministic
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocolToDeterministicComplexity

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.newmanProtocol_complexity

Topic: communication   Node: c540bbfa0c1a

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.newmanProtocol_complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Newman.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Communication cost of the Newman protocol. Let $X$ and $Y$ be finite types, let $\Omega$ be a finite probability space, and let $p$
be a public-coin finite-message protocol over $\Omega$ with private inputs in $X$ and
$Y$ and outputs in a type $\alpha$. Fix a target function $f : X \to Y \to \alpha$, real
parameters $\varepsilon$ and $c$ with $c > 1$, and suppose that $p$
$\varepsilon$-computes $f$. Then the communication complexity of the associated Newman
protocol equals
\[
  \left\lceil \log_2 t(X, Y, \varepsilon, c) \right\rceil + \mathrm{complexity}(p),
\]
where $t(X, Y, \varepsilon, c)$ is the derandomization sample count and
$\mathrm{complexity}(p)$ is the communication complexity of $p$; that is, running the
Newman protocol costs exactly the cost of $p$ together with the number of bits Alice
needs to name one seed in the table of size $t(X, Y, \varepsilon, c)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- The communication complexity of the Newman protocol is `⌈log₂ (derandomizationSamples X Y ε c)⌉ + complexity of p`: Alice's index costs `⌈log₂ t⌉` bits, after which the simulated deterministic protocol costs exactly what `p` costs. [RY20, Thm 3.5 proof]. The proof unfolds the protocol and evaluates the supremum over indices of a constant function. -/
theorem CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.newmanProtocol_complexity
    {Ω X Y α : Type*} [FiniteProbabilitySpace Ω]
    [Fintype X] [Fintype Y]
    (p : FiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    (p.newmanProtocol f ε c hc hp).complexity =
      Nat.clog 2 (FiniteMessage.Protocol.derandomizationSamples
        X Y ε c) + p.complexity := by
  unfold newmanProtocol PrivateCoin.FiniteMessage.Protocol.alice
  simp only [Deterministic.FiniteMessage.Protocol.complexity,
    Deterministic.FiniteMessage.Protocol.toPrivateCoin_complexity,
    PublicCoin.FiniteMessage.Protocol.toDeterministic_complexity]
  -- sup of constant function = constant (since newmanIndexSpace is nonempty)
  rw [Finset.sup_const
    (α := ℕ) (Finset.univ_nonempty (α := newmanIndexSpace X Y ε c)),
    show Fintype.card (newmanIndexSpace X Y ε c) =
      FiniteMessage.Protocol.derandomizationSamples X Y ε c
      from Fintype.card_fin _]
