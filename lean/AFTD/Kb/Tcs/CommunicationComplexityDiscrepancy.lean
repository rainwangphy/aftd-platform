import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityBoolSign
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.discrepancy

Topic: communication   Node: 59154f734579

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.discrepancy`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Let $\mu$ be a finite probability space on $X \times Y$, let $g : X \to Y \to
\mathrm{Bool}$, and let $S \subseteq X \times Y$.  The \emph{discrepancy} of $g$ on $S$
with respect to $\mu$ is
\[
  \mathrm{disc}_\mu(g, S)
  \;=\;
  \mathbb{E}_{(x,y)\sim\mu}\bigl[\mathbf{1}_{S}(x,y)\cdot\sigma(g(x,y))\bigr],
\]
where $\sigma : \mathrm{Bool} \to \{-1,1\}$ is the sign map \texttt{CommunicationComplexity.boolSign}.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
/-- The discrepancy of a Boolean function `g` on a subset `S ⊆ X × Y` with respect to a distribution `μ` on `X × Y`: the expectation under `μ` of the indicator of `S` times the `±1` sign of `g`, i.e. the `μ`-mass of the `false` part of `S` minus the `μ`-mass of its `true` part. [RY20, Ch. 5, Definition (Discrepancy)]. Deviation: taken relative to an arbitrary finite distribution `μ` on `X × Y` (RY20 takes the expectation over "a random input x", uniform in its applications such as Thm 5.6), and defined as the signed expectation, without RY20's absolute value; the sign convention `boolSign` (`false ↦ 1`, `true ↦ −1`) agrees with RY20's `(−1)^{g(x)}`. The lower bounds below use `|discrepancy g R|`. -/
noncomputable def CommunicationComplexity.discrepancy
    [μ : FiniteProbabilitySpace (X × Y)]
    (g : X → Y → Bool)
    (S : Set (X × Y)) : ℝ := by
  classical
  exact ∫ xy : X × Y,
    (if xy ∈ S then (1 : ℝ) else 0) * boolSign (g xy.1 xy.2)
