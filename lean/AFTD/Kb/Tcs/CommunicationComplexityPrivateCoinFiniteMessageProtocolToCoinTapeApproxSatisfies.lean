import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToCoinTape
import AFTD.Kb.Tcs.CommunicationComplexityInternalProductCoinApprox
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolApproxSatisfies
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToCoinTapeComplexity
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrunEq
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeIsProbabilityMeasure
import AFTD.Kb.Tcs.CommunicationComplexityCoinTapeFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityInstProd
import AFTD.Kb.Tcs.CommunicationComplexityInstPi
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun

/-!
# CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape_approxSatisfies

Topic: communication   Node: 89f223ef3f23

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape_approxSatisfies`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Coin-tape conversion preserves approximate correctness. Let $p$ be a private-coin finite-message protocol over input types $X$, $Y$ and output
type $\alpha$, whose private randomness for Alice and Bob is drawn from finite
probability spaces $\Omega_X$ and $\Omega_Y$. Let $Q : X \to Y \to \alpha \to
\mathrm{Prop}$ be a predicate on input–output triples, and let $\varepsilon$ and
$\delta$ be real numbers with $\delta > 0$. Suppose $p$ $\varepsilon$-satisfies $Q$;
that is, for every input pair $(x, y)$ the probability, over Alice's and Bob's private
coins $(\omega_x, \omega_y)$, that the output of $p$ fails to satisfy $Q\,x\,y$ is at
most $\varepsilon$. Then the protocol obtained by converting $p$ at tolerance $\delta$ —
replacing the private randomness by fair coin tapes of some lengths $n_X$ and $n_Y$ —
$(\varepsilon + \delta)$-satisfies $Q$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- If a private-coin finite-message protocol `p` satisfies the predicate `Q` on every input except with probability at most `ε`, then its coin-tape approximation with slack `δ` satisfies `Q` on every input except with probability at most `ε + δ`. This is the discretisation step of Newman's theorem [New91]. **Proof sketch.** Fix an input `(x, y)` and unfold the construction to expose the maps `φ_X`, `φ_Y` and their approximation property. The set of coin tapes on which the approximating protocol violates `Q` is the preimage under `(φ_X, φ_Y)` of the set `S` of coins on which `p` violates `Q`. By `product_coin_approx` the probability of that preimage is at most `vol S + δ`, and `vol S ≤ ε` by hypothesis. -/
theorem CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.toCoinTape_approxSatisfies
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (Q : X → Y → α → Prop)
    (ε δ : ℝ) (hδ : 0 < δ)
    (hp : p.ApproxSatisfies Q ε) :
    (p.toCoinTape δ hδ).2.2.ApproxSatisfies Q (ε + δ) := by
  intro x y
  simp only [FiniteMessage.Protocol.toCoinTape]
  -- Extract the approximation data
  set data := Internal.product_coin_approx (Ω_X := Ω_X) (Ω_Y := Ω_Y) δ hδ
  set φ_X := data.choose_spec.choose_spec.choose
  set φ_Y := data.choose_spec.choose_spec.choose_spec.choose
  have happrox := data.choose_spec.choose_spec.choose_spec.choose_spec
  -- The error set under the new protocol is the preimage under (φ_X, φ_Y)
  let S := {ω : Ω_X × Ω_Y | ¬Q x y (p.rrun x y ω.1 ω.2)}
  have hset : {ω : CoinTape data.choose × CoinTape data.choose_spec.choose |
      ¬Q x y (FiniteMessage.Protocol.rrun
        (p.comap (Prod.map φ_X id) (Prod.map φ_Y id)) x y ω.1 ω.2)} =
      Prod.map φ_X φ_Y ⁻¹' S := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Prod.map, S,
      FiniteMessage.Protocol.rrun,
      Deterministic.FiniteMessage.Protocol.comap_run, Function.id_def]
  rw [hset]
  calc volume.real (Prod.map φ_X φ_Y ⁻¹' S :
          Set (CoinTape data.choose × CoinTape data.choose_spec.choose))
      ≤ volume.real S + δ := happrox S
    _ ≤ ε + δ := by
        have hpS : volume.real S ≤ ε := by simpa [S] using hp x y
        linarith
