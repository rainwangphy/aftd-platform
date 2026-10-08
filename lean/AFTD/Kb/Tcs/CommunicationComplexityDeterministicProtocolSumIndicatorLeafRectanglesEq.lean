import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesIsMonoPartition
import AFTD.Kb.Tcs.CommunicationComplexityBoolSign
import AFTD.Kb.Tcs.CommunicationComplexityRectangleMonoPartitionPartUnique
import AFTD.Kb.Tcs.CommunicationComplexityRectangleMonoPartitionPointMem
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesFinset
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolMemLeafRectanglesFinset
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRectangleSign
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRectangleSignEqBoolSign
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityBoolSignXor
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolRun

/-!
# CommunicationComplexity.Deterministic.Protocol.sum_indicator_leafRectangles_eq

Topic: communication   Node: 6516505b5c2c

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.sum_indicator_leafRectangles_eq`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Indicator sum over leaf rectangles recovers the protocol output. Let $X$ and $Y$ be input types whose product $X \times Y$ carries a finite probability
space, and let $p$ be a deterministic Boolean two-party protocol over $X$ (Alice) and
$Y$ (Bob). Write $\{R\}$ for the finite collection of leaf rectangles of $p$, and for
each such rectangle assign the sign $\varepsilon(R) = +1$ if $p$ outputs
$\mathrm{false}$ at every point of $R$ and $\varepsilon(R) = -1$ otherwise. Then for
every point $(x,y) \in X \times Y$,
\[
\sum_{R} \mathbf{1}_R(x,y)\,\varepsilon(R) \;=\; \begin{cases} 1 & \text{if } p(x,y) =
\mathrm{false},\\ -1 & \text{if } p(x,y) = \mathrm{true},\end{cases}
\]
where $p(x,y)$ denotes the Boolean value returned by running $p$ on inputs $x$ and $y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
open Classical in
/-- Summing, over the leaf rectangles `R` of `p`, the indicator of `R` weighted by the rectangle sign of `R` gives the `±1` sign of the protocol's output at every point: the leaf rectangles partition `X × Y`, so exactly one term is nonzero. -/
lemma CommunicationComplexity.Deterministic.Protocol.sum_indicator_leafRectangles_eq
    [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol X Y Bool) (xy : X × Y) :
    Finset.sum (leafRectanglesFinset p)
      (fun R => Set.indicator R (fun _ => rectangleSign p R) xy) =
      boolSign (p.run xy.1 xy.2) := by
  classical
  let hPart := leafRectangles_isMonoPartition p p.run rfl
  obtain ⟨R, hR, hxyR⟩ := Rectangle.monoPartition_point_mem hPart xy
  have hR' : R ∈ leafRectanglesFinset p := by
    exact (mem_leafRectanglesFinset p R).2 hR
  rw [Finset.sum_eq_single_of_mem R hR']
  · simp [hxyR, rectangleSign_eq_boolSign p hR hxyR]
  · intro S hS hSR
    have hxyS : xy ∉ S := by
      intro hxyS
      have hEq :=
        Rectangle.monoPartition_part_unique hPart hR ((mem_leafRectanglesFinset p S).1 hS) hxyR hxyS
      exact hSR hEq.symm
    simp [hxyS]
