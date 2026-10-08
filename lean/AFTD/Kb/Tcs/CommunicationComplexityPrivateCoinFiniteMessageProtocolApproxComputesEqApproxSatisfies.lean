import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolApproxComputes
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocolApproxSatisfies

/-!
# CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies

Topic: communication   Node: 3d8da6dac693

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinFiniteMessage.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Approximate computation as approximate satisfaction of equality. Let $p$ be a private-coin finite-message protocol over input types $X$, $Y$ with
private-randomness types $\Omega_X$, $\Omega_Y$ and output type $\alpha$, each of
$\Omega_X$ and $\Omega_Y$ carrying a measure, let $f : X \times Y \to \alpha$ be a
target function, and let $\varepsilon \in \bbr$. Then the proposition that $p$
$\varepsilon$-computes $f$ coincides with the proposition that $p$
$\varepsilon$-satisfies the predicate $Q(x,y,a)$ given by $a = f(x,y)$; that is, the two
propositions are equal.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {Ω_X Ω_Y : Type*} {X Y α : Type*} in
/-- A private-coin finite-message protocol `ε`-computes `f` if and only if it `ε`-satisfies the relation "the output on `(x, y)` equals `f x y`"; the two propositions are equal. -/
theorem CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol.ApproxComputes_eq_ApproxSatisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) :
    p.ApproxComputes f ε =
      p.ApproxSatisfies (fun x y a => a = f x y) ε := by
  simp only [ApproxComputes, ApproxSatisfies, ne_eq]
