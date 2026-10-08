import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwap

/-!
# CommunicationComplexity.Deterministic.Protocol.swap_swap

Topic: communication   Node: fdb18c8df978

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.swap_swap`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Role swap is an involution. Let $p$ be a deterministic two-party communication protocol with Alice's inputs drawn
from a type $X$, Bob's from a type $Y$, and outputs in a type $\alpha$. Applying the
role swap twice — first exchanging the roles of Alice and Bob throughout $p$, then
exchanging them again — returns the original protocol $p$ unchanged.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Swapping Alice and Bob twice returns the original protocol. -/
@[simp]
theorem CommunicationComplexity.Deterministic.Protocol.swap_swap (p : Protocol X Y α) :
    p.swap.swap = p := by
  induction p <;> simp [swap, *]
