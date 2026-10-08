import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSwap

/-!
# CommunicationComplexity.Deterministic.Protocol.swap_run

Topic: communication   Node: d082ba399af1

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.swap_run`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Role swap preserves protocol output. Let $p$ be a deterministic two-party communication protocol with Alice's inputs drawn
from $X$, Bob's inputs drawn from $Y$, and outputs in $\alpha$, and let $x : X$ and $y :
Y$ be inputs. Then executing the role-swapped protocol on the input pair $(y, x)$
returns the same value as executing $p$ on $(x, y)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Running the swapped protocol on `(y, x)` gives the same output as running the original protocol on `(x, y)`. -/
@[simp]
theorem CommunicationComplexity.Deterministic.Protocol.swap_run (p : Protocol X Y α) (x : X) (y : Y) :
    p.swap.run y x = p.run x y := by
  induction p <;> simp [swap, run, *]
