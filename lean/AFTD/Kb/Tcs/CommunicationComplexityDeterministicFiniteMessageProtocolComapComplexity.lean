import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolToProtocolExists

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_complexity

Topic: communication   Node: bd8fc183dc7a

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_complexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pullback preserves communication complexity. Let $p$ be a finite-message deterministic communication protocol over input types $X$
and $Y$ with output type $\alpha$, and let $f_X : X' \to X$ and $f_Y : Y' \to Y$ be maps
of input types. Then the pullback protocol obtained by precomposing every message
function of $p$ with $f_X$ or $f_Y$ (as appropriate) has the same communication
complexity as $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Pulling a finite-message protocol back along input maps does not change its complexity. -/
@[simp]
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_complexity {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    (p.comap fX fY).complexity = p.complexity := by
  induction p <;> simp [comap, complexity, *]
