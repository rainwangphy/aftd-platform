import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComapRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComapComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxMono

/-!
# CommunicationComplexity.Deterministic.Protocol.comap_run

Topic: communication   Node: a75a3d6e12a9

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.comap_run`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pull-back commutes with protocol execution. Let $p$ be a deterministic two-party communication protocol with Alice's inputs drawn
from $X$ and Bob's from $Y$, producing values in $\alpha$, and let $f_X : X' \to X$ and
$f_Y : Y' \to Y$ be arbitrary maps of input types. Then for all $x' \in X'$ and $y' \in
Y'$, running the pull-back of $p$ along $f_X$ and $f_Y$ on the inputs $x'$ and $y'$
yields the same output as running $p$ itself on the transported inputs $f_X(x')$ and
$f_Y(y')$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Running the pulled-back protocol on `(x', y')` gives the same output as running the original protocol on `(fX x', fY y')`. -/
@[simp]
theorem CommunicationComplexity.Deterministic.Protocol.comap_run {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y)
    (x' : X') (y' : Y') :
    (p.comap fX fY).run x' y' = p.run (fX x') (fY y') := by
  induction p <;> simp [comap, run, *]
