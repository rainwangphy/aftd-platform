import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComap

/-!
# CommunicationComplexity.Deterministic.Protocol.comap_complexity

Topic: communication   Node: 845d7444e581

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.comap_complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pull-back preserves communication complexity. Let $p$ be a deterministic two-party communication protocol with Alice's inputs drawn
from $X$, Bob's inputs from $Y$, and outputs in $\alpha$, and let $f_X : X' \to X$ and
$f_Y : Y' \to Y$ be maps re-indexing the two input types. Then the pull-back protocol
over $X'$ and $Y'$ obtained by pre-composing each of Alice's message functions with
$f_X$ and each of Bob's message functions with $f_Y$ has the same communication
complexity as $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Pulling a protocol back along input maps does not change its complexity. -/
@[simp]
theorem CommunicationComplexity.Deterministic.Protocol.comap_complexity {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    (p.comap fX fY).complexity = p.complexity := by
  induction p <;> simp [comap, complexity, *]
