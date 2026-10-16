import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolExistsGoodRandomness
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceMeasureRealProd
import AFTD.Kb.Tcs.CommunicationComplexityUniformOnUnivMeasureRealEqCardFilter
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolNewmanProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpace
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolAlice
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToPrivateCoinRrun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToDeterministicRun
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToDeterministicComplexity
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
import AFTD.Kb.Tcs.CommunicationComplexityUnitMeasureSpace
import AFTD.Kb.Tcs.CommunicationComplexityUnitFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceFintype
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceNonempty
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceMeasureSpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceIsProbabilityMeasure
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolToDeterministic
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToPrivateCoin
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolDerandomizationSamples
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolRrun

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.newmanProtocol_ApproxComputes

Topic: communication   Node: 8dbe3b1cd134

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.newmanProtocol_ApproxComputes`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Newman.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Newman's reduction preserves approximate correctness. Let $\Omega$ be a finite probability space, let $X$ and $Y$ be finite types, and let $p$
be a public-coin finite-message protocol over shared randomness $\Omega$ with inputs in
$X$ and $Y$ and outputs in a type $\alpha$. Fix a target function $f : X \times Y \to
\alpha$, a real error bound $\varepsilon$, and a real constant $c > 1$, and suppose that
$p$ $\varepsilon$-computes $f$, meaning that for every input pair $(x,y)$ the
probability over the shared randomness that $p$ outputs something other than $f(x,y)$ is
at most $\varepsilon$. Then the associated Newman protocol — the private-coin protocol
in which Alice draws an index into the fixed table of good random seeds, sends it to
Bob, and both run $p$ deterministically on that seed — $(c\varepsilon)$-computes $f$:
for every input pair $(x,y)$ the probability over the private randomness that its output
differs from $f(x,y)$ is at most $c\varepsilon$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- The Newman protocol built from a public-coin protocol `p` that ε-computes `f` computes `f` with error at most `c · ε` on every input: for all `x`, `y`, the probability over Alice's random index that the protocol's output differs from `f x y` is at most `c · ε`. [RY20, Thm 3.5 proof]. **Proof sketch.** Fix an input `(x, y)` and let `ωs` be the table of good seeds. After unfolding, the protocol's output on private randomness `(i, ())` is the output of `p` on seed `ωs i`. Step 1: the error event on the product space `newmanIndexSpace × Unit` is the product of the set of bad indices (those `i` for which `p` errs on seed `ωs i`) with the whole of `Unit`. Step 2: by the product formula for the measure and since `Unit` has total mass one, the error probability equals the uniform measure of the bad-index set. Step 3: the uniform measure of a set of indices is its cardinality divided by `t`, which is at most `c · ε` by the defining property of the good table. -/
theorem CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.newmanProtocol_ApproxComputes
    {Ω X Y α : Type*} [FiniteProbabilitySpace Ω]
    [Fintype X] [Fintype Y]
    (p : FiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    (p.newmanProtocol f ε c hc hp).ApproxComputes f (c * ε) := by
  -- ApproxComputes means: for all x y, P[rrun ≠ f x y] ≤ c * ε
  -- on the product space newmanIndexSpace × Unit
  intro x y
  -- Unfold the protocol definition to get at the run behavior
  unfold newmanProtocol PrivateCoin.FiniteMessage.Protocol.alice
  simp only [PrivateCoin.FiniteMessage.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.run,
    Deterministic.FiniteMessage.Protocol.comap_run]
  set ωs := (exists_good_randomness p f ε c hc hp).choose
  have hωs := (exists_good_randomness p f ε c hc hp).choose_spec
  -- Step 1: the error set only depends on ω.1 (the index)
  have hset : {ω : newmanIndexSpace X Y ε c × Unit |
      p.run (ωs ω.1, x) (ωs ω.1, y) ≠ f x y} =
      {i | p.run (ωs i, x) (ωs i, y) ≠ f x y} ×ˢ Set.univ := by
    ext ⟨i, u⟩; simp
  rw [hset]
  -- Step 2: identify the product-space error probability with the measure of the bad
  -- index set.
  erw [FiniteProbabilitySpace.measureReal_prod]
  rw [probReal_univ, mul_one]
  let BadIdx : Set (newmanIndexSpace X Y ε c) :=
    {i | p.run (ωs i, x) (ωs i, y) ≠ f x y}
  -- Step 3: compute that measure in the uniform index space by cardinality and apply
  -- the good-table bound.
  rw [Measure.real]
  change (((ProbabilityTheory.uniformOn Set.univ : Measure (newmanIndexSpace X Y ε c))
    BadIdx).toReal ≤ c * ε)
  rw [uniformOn_univ_measureReal_eq_card_filter
    (Ω := newmanIndexSpace X Y ε c) BadIdx]
  simp only [ne_eq, Set.mem_setOf_eq, Fintype.card_fin, BadIdx]
  convert hωs x y using 1
  congr 1
  simp [ωs]
  congr
