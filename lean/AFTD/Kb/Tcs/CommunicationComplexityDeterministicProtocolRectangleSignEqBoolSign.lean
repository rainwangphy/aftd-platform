import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesMono
import AFTD.Kb.Tcs.CommunicationComplexityBoolSign
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRectangleSign

/-!
# CommunicationComplexity.Deterministic.Protocol.rectangleSign_eq_boolSign

Topic: communication   Node: 4e8fe5979098

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.rectangleSign_eq_boolSign`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Rectangle sign equals Boolean sign on leaf rectangles. Let $p$ be a deterministic two-party communication protocol with Boolean output, over
input types $X$ (Alice) and $Y$ (Bob). If $R$ is a leaf rectangle of $p$ and $(x, y)$ is
any point of $R$, then the rectangle sign of $R$ agrees with the Boolean sign of the
value that $p$ computes on $(x, y)$: it equals $+1$ when $p$ outputs $\mathrm{false}$ at
$(x, y)$ and $-1$ when $p$ outputs $\mathrm{true}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
/-- On a leaf rectangle `R` of `p`, the rectangle sign of `R` equals the `±1` sign of the protocol's output at any point of `R` (the output is constant on leaf rectangles). **Proof sketch.** Case on whether the protocol outputs `false` at every point of `R`. If so, the rectangle sign is `1` and so is the sign of the output at `xy`. Otherwise the output is constant on the leaf rectangle (`leafRectangles_mono`), so it cannot be `false` at `xy` (it would then be `false` on all of `R`); hence it is `true` and both sides equal `-1`. -/
lemma CommunicationComplexity.Deterministic.Protocol.rectangleSign_eq_boolSign
    (p : Protocol X Y Bool)
    {R : Set (X × Y)} (hR : R ∈ p.leafRectangles)
    {xy : X × Y} (hxy : xy ∈ R) :
    rectangleSign p R = boolSign (p.run xy.1 xy.2) := by
  classical
  by_cases hfalse : ∀ z ∈ R, p.run z.1 z.2 = false
  · rw [rectangleSign, if_pos hfalse]
    simp [boolSign, hfalse xy hxy]
  · have hmono := leafRectangles_mono p p.run rfl R hR
    have htrue : p.run xy.1 xy.2 = true := by
      cases hrun : p.run xy.1 xy.2 with
      | false =>
          exfalso
          apply hfalse
          intro z hz
          rw [hmono z.1 xy.1 z.2 xy.2 hz hxy, hrun]
      | true =>
          rfl
    · rw [rectangleSign, if_neg hfalse]
      simp [boolSign, htrue]
