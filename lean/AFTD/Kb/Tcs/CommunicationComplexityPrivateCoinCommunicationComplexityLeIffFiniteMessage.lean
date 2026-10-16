import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolOfProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolOfProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinCommunicationComplexityLeIff
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolOfProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToCoinTapeComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolOfProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolOfProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeIsProbabilityMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolOfProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolOfProtocolComplexity

/-!
# CommunicationComplexity.PrivateCoin.communicationComplexity_le_iff_finiteMessage

Topic: communication   Node: 990d8c189d3e

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PrivateCoin.communicationComplexity_le_iff_finiteMessage`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComplexity.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finite-message characterization of private-coin complexity. Let $f : X \to Y \to \alpha$ be a function, let $\varepsilon \in \bbr$ be an error
bound, and let $n \in \bbn$. Then the $\varepsilon$-error private-coin randomized
communication complexity satisfies $R_\varepsilon(f) \le n$ if and only if there exist
coin-tape lengths $n_X, n_Y \in \bbn$ and a private-coin finite-message protocol $p$
with randomness spaces $\{0,1\}^{n_X}$ and $\{0,1\}^{n_Y}$ (over input types $X$, $Y$
and output type $\alpha$) such that $p$ computes $f$ with error at most $\varepsilon$ on
every input pair and has worst-case communication cost at most $n$. Thus the
private-coin complexity, defined via binary-message protocols, is unchanged when one
instead allows protocols whose players may send elements of arbitrary finite nonempty
message alphabets, each $\beta$-valued message being charged $\lceil \log_2 \abs{\beta}
\rceil$ bits.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- The `ε`-error private-coin communication complexity of `f` is at most `n` if and only if there is a private-coin *finite-message* protocol, over coin tapes of some lengths `nX`, `nY`, that `ε`-computes `f` with complexity at most `n`. Both directions convert the protocol with `ofProtocol` / `toProtocol`, which preserve the run function and the complexity. **Proof sketch.** Rewrite the left side (`communicationComplexity_le_iff`) as the existence of a binary protocol that `ε`-computes `f` with complexity at most the bound. Forward: given a binary protocol, `ofProtocol` yields a finite-message protocol with the same run on every input and the same complexity, so the error bound and the complexity bound carry over. Backward: `toProtocol` turns a finite-message protocol into a binary one; unfolding the failure event on each input and rewriting with `toProtocol_run` shows the error is unchanged, and the complexity is preserved. -/
theorem CommunicationComplexity.PrivateCoin.communicationComplexity_le_iff_finiteMessage
    {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    communicationComplexity f ε ≤ n ↔
      ∃ (nX nY : ℕ)
        (p : FiniteMessage.Protocol (CoinTape nX) (CoinTape nY) X Y α),
        p.ApproxComputes f ε ∧
        p.complexity ≤ n := by
  rw [communicationComplexity_le_iff]
  constructor
  · -- Binary → FiniteMessage via ofProtocol
    rintro ⟨nX, nY, p, hp, hc⟩
    refine ⟨nX, nY, FiniteMessage.Protocol.ofProtocol p, ?_,
      Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p ▸ hc⟩
    intro x y
    simp only [FiniteMessage.Protocol.rrun,
      Deterministic.FiniteMessage.Protocol.ofProtocol_run]
    exact hp x y
  · -- FiniteMessage → Binary via toProtocol
    rintro ⟨nX, nY, p, hp, hc⟩
    refine ⟨nX, nY, p.toProtocol, ?_,
      Deterministic.FiniteMessage.Protocol.toProtocol_complexity p ▸ hc⟩
    intro x y
    change (volume {ω : CoinTape nX × CoinTape nY |
      Deterministic.Protocol.run (Deterministic.FiniteMessage.Protocol.toProtocol p)
        (ω.1, x) (ω.2, y) ≠ f x y}).toReal ≤ ε
    simp only [Deterministic.FiniteMessage.Protocol.toProtocol_run]
    exact hp x y
