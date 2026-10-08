import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolOfProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_run

Topic: communication   Node: 0857c8a1ad83

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_run`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Embedding preserves protocol output. Let $X$ and $Y$ be the input types of Alice and Bob, let $\alpha$ be an output type, and
let $p$ be a deterministic binary two-party communication protocol producing values in
$\alpha$. Regard $p$ as a finite-message protocol by treating each of its Boolean
messages as an element of the two-element type. Then for all inputs $x \in X$ and $y \in
Y$, executing this embedded finite-message protocol on $x$ and $y$ yields the same value
in $\alpha$ as executing $p$ directly on $x$ and $y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Viewing a binary protocol as a finite-message protocol does not change its outcome on any input. -/
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.ofProtocol_run (p : Deterministic.Protocol X Y α) (x : X) (y : Y) :
    (ofProtocol p).run x y = p.run x y := by
  induction p <;> simp [ofProtocol, run, Deterministic.Protocol.run, *]
