import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsIndexingIndexing
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolCost
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayLeCommunicationComplexityIff
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicLeCommunicationComplexityIff
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun

/-!
# CommunicationComplexity.Functions.Indexing.le_oneWayCommunicationComplexity

Topic: communication   Node: 746dbcd6d7ca

Provenance: formalization of a published result. Source: One-way complexity of Index is at least $n$, as formalized in TCSlib (`CommunicationComplexity.Functions.Indexing.le_oneWayCommunicationComplexity`). Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/Basic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

One-way complexity of Index is at least $n$. Every correct deterministic one-way protocol for $\mathrm{IND}_n$ has cost at least $n$;
that is,
\[
  n \le D^{\to}(\mathrm{IND}_n).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open CommunicationComplexity.Deterministic in
open MeasureTheory ProbabilityTheory in
open scoped BigOperators in
variable (n : ℕ+) in
/-- Every correct deterministic one-way protocol for Index on `n` bits has cost at least `n`; that is, `n ≤ D→(IND_n)` [Rou16, Prop 1.8] (pigeonhole on Alice's messages; Rou16 states it for Disjointness, and the proof for Index is identical). Together with `oneWayCommunicationComplexity_le` this gives the exact value `n`, whereas Rou16 only states the lower bound. **Proof sketch.** Fix a correct one-way protocol `p`. Alice's message map `send` is injective: if `send x = send y` then Bob's decoded answers agree on every index `i`, and by correctness these are `x i` and `y i`, so `x = y`. Hence the number of messages is at least the number of strings, `2^n`. On the other hand a protocol of cost `c` has at most `2^c` messages. So `2^n ≤ 2^c`, which forces `n ≤ c`. -/
theorem CommunicationComplexity.Functions.Indexing.le_oneWayCommunicationComplexity : n ≤ OneWay.communicationComplexity (indexing n) := by
  rw [OneWay.le_communicationComplexity_iff]
  intro p hp_comp
  -- Step 1: Alice's message map is injective, by correctness of Bob's decoding.
  have hinj : Function.Injective p.send := by
    intro x y heq
    ext i
    have hx := congrFun (congrFun hp_comp x) i
    have hy := congrFun (congrFun hp_comp y) i
    have hm : p.decode (p.send x) i = p.decode (p.send y) i := by
      simpa using congrArg (fun m => p.decode m i) heq
    simpa [OneWay.Protocol.Computes, OneWay.Protocol.run, indexing] using
      hx.symm.trans (hm.trans hy)
  -- Step 2: hence there are at least `2^n` messages.
  have hcard : Fintype.card (Fin n → Bool) ≤ Fintype.card p.Message := by
    exact Fintype.card_le_of_injective p.send hinj
  have hpow_dom : 2 ^ (n : ℕ) ≤ Fintype.card p.Message := by
    simpa [Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] using hcard
  -- Step 3: a protocol of cost `c` has at most `2^c` messages.
  have hcost : Fintype.card p.Message ≤ 2 ^ p.cost := by
    apply Nat.le_pow_clog; linarith
  -- Step 4: `2^n ≤ 2^c` forces `n ≤ c`.
  by_contra!
  have h_bad : 2 ^ p.cost < 2 ^ (n : ℕ) := by
    refine Nat.pow_lt_pow_of_lt (by linarith) this
  omega
