import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRectangleSign

/-!
# CommunicationComplexity.Deterministic.Protocol.rectangleSign_abs

Topic: communication   Node: 20ac86222493

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.rectangleSign_abs`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Rectangle sign has absolute value one. Let $p$ be a deterministic Boolean two-party communication protocol on input types $X$
(Alice) and $Y$ (Bob), and let $R \subseteq X \times Y$ be any set. Define the rectangle
sign of $p$ on $R$ to be $+1$ when $p$ outputs $\mathrm{false}$ at every point of $R$
and $-1$ otherwise. Then the rectangle sign has absolute value $1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
/-- The rectangle sign has absolute value `1`. -/
lemma CommunicationComplexity.Deterministic.Protocol.rectangleSign_abs
    (p : Protocol X Y Bool) (R : Set (X × Y)) :
    |rectangleSign p R| = 1 := by
  classical
  rw [rectangleSign]
  split_ifs <;> norm_num
