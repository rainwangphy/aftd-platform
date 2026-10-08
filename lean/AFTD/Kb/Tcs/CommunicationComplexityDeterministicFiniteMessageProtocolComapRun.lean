import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComap
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun

/-!
# CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run

Topic: communication   Node: da76f204d0d7

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Execution commutes with pullback. Let $p$ be a finite-message deterministic communication protocol over input types $X$,
$Y$ with output type $\alpha$, and let $f_X : X' \to X$ and $f_Y : Y' \to Y$ be maps
into those input types. Then for every pair of inputs $x' : X'$ and $y' : Y'$, executing
the pullback protocol $p.\mathrm{comap}\,f_X\,f_Y$ on $(x', y')$ yields the same output
as executing $p$ on the transported inputs $(f_X(x'), f_Y(y'))$; that is,
\[
\mathrm{run}\bigl(p.\mathrm{comap}\,f_X\,f_Y\bigr)(x', y') \;=\;
\mathrm{run}(p)\bigl(f_X(x'),\, f_Y(y')\bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Running the pulled-back protocol on `(x', y')` gives the same output as running the original protocol on `(fX x', fY y')`. -/
@[simp]
theorem CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y)
    (x' : X') (y' : Y') :
    (p.comap fX fY).run x' y' = p.run (fX x') (fY y') := by
  induction p <;> simp [comap, run, *]
