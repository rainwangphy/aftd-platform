import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolEncodeAlice
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolRun

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_exists

Topic: communication   Node: 6d9e1a70ded6

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_exists`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Binary simulation of a finite-message protocol. Let $X$, $Y$, and $\alpha$ be types, and let $p$ be a finite-message two-party protocol
over inputs $X$ (Alice) and $Y$ (Bob) with output type $\alpha$, in which each message
ranges over an arbitrary finite nonempty type and a $\beta$-valued message is charged
$\lceil \log_2 |\beta| \rceil$ bits. Then there exists a binary deterministic protocol
$P$ over the same input types $X$, $Y$ and output type $\alpha$ — one in which every
message is a single bit — that computes the same function, i.e.\ $P$ and $p$ return the
same output on every pair of inputs, and has exactly the same communication complexity
as $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Every finite-message protocol is simulated by a binary protocol with the same outcome function and the same complexity. The Alice case is `encode_alice`; the Bob case is reduced to it by swapping the players. **Proof sketch.** Induction on the protocol. An output leaf is its own binary protocol. At an Alice node, the induction hypothesis chooses a binary continuation for every message; encoding the message (`encode_alice`) gives a binary protocol whose run and complexity agree with the node's. At a Bob node, swap the players in every continuation, apply the Alice case, and swap the result back; swapping preserves both run and complexity. -/
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.toProtocol_exists
    (p : Protocol X Y α) :
    ∃ (P : Deterministic.Protocol X Y α),
      P.run = p.run ∧ P.complexity = p.complexity := by
  induction p with
  | output val => exact ⟨Deterministic.Protocol.output val, rfl, rfl⟩
  | @alice β _ _ f P ih =>
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ := encode_alice f Q
    exact ⟨R,
      funext₂ fun x y => by rw [hR_run, hQ_run, Deterministic.FiniteMessage.Protocol.run],
      by rw [hR_comp]; simp [Deterministic.FiniteMessage.Protocol.complexity, hQ_comp]⟩
  | @bob β _ _ f P ih =>
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ := encode_alice f (fun b => (Q b).swap)
    exact ⟨R.swap,
      funext₂ fun x y => by
        simp [Deterministic.FiniteMessage.Protocol.run,
          Deterministic.Protocol.swap_run, hR_run, hQ_run],
      by simp [Deterministic.FiniteMessage.Protocol.complexity,
          Deterministic.Protocol.swap_complexity, hR_comp,
          Deterministic.Protocol.swap_complexity, hQ_comp]⟩
