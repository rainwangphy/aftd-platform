import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwap

/-!
# CommunicationComplexity.Deterministic.Protocol.swap_complexity

Topic: communication   Node: f60b21f4d62c

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.swap_complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Role swap preserves communication complexity. Let $p$ be a deterministic two-party communication protocol with Alice's inputs drawn
from a type $X$, Bob's from a type $Y$, and outputs in a type $\alpha$. Let
$p^{\mathrm{swap}}$ be the protocol obtained by interchanging the roles of Alice and Bob
throughout — turning every Alice node into a Bob node and vice versa while leaving
output nodes unchanged. Then $p^{\mathrm{swap}}$ has the same communication complexity
as $p$: the worst-case number of bits exchanged is unaffected by the swap.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Swapping the roles of Alice and Bob does not change the complexity of a protocol. -/
@[simp]
theorem CommunicationComplexity.Deterministic.Protocol.swap_complexity (p : Protocol X Y α) :
    p.swap.complexity = p.complexity := by
  induction p <;> simp [swap, complexity, *]
