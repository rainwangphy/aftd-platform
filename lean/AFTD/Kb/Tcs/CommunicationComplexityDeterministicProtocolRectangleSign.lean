import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun

/-!
# CommunicationComplexity.Deterministic.Protocol.rectangleSign

Topic: communication   Node: 3444361fc0f7

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Protocol.rectangleSign`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a deterministic Boolean protocol $p$ and a set $R \subseteq X \times Y$, the
\emph{rectangle sign} is $+1$ if the protocol outputs $\mathrm{false}$ on every point of
$R$, and $-1$ otherwise.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
/-- The sign attached to a rectangle in the leaf partition of a Boolean protocol: it is `1` when the protocol outputs `false` on that rectangle, and `-1` otherwise. -/
noncomputable def CommunicationComplexity.Deterministic.Protocol.rectangleSign
    (p : Protocol X Y Bool) (R : Set (X × Y)) : ℝ := by
  classical
  exact if ∀ xy ∈ R, p.run xy.1 xy.2 = false then 1 else -1
