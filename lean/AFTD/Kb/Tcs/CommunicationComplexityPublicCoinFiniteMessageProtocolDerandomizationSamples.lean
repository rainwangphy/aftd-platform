import AFTD.Prelude

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.derandomizationSamples

Topic: communication   Node: f317c702ca7c

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.derandomizationSamples`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Derandomization.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given finite types $X$ and $Y$ and real parameters $\varepsilon, c$, the number of random
samples required for derandomization via Chernoff and union bound is
\[
  t(X, Y, \varepsilon, c) \;=\;
  \left\lceil
    \frac{\log(|X|\cdot|Y|)}{2\,(c-1)^2\,\varepsilon^2}
  \right\rceil_{\!+} + 1,
\]
where $\lceil\cdot\rceil_{+}$ denotes the natural-number ceiling.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
variable {Ω X Y α : Type*}
  [Fintype X] [Fintype Y] in
/-- The number `t` of seeds sampled in the derandomization step of Newman's theorem, `⌈log(|X|·|Y|) / (2·(c-1)²·ε²)⌉₊ + 1`; it is chosen so that `|X|·|Y| · exp(−2 (c−1)² ε² t) < 1`. [RY20, Thm 3.5 proof] (`t = O(n/ε²)` sample strings) / [Rou16, Thm 4.9 proof]. Deviation: the count is made explicit as `derandomizationSamples X Y ε c` for arbitrary finite input types `X`, `Y` and a slack factor `c > 1` on the error, rather than the textbook `O(n/ε²)`. -/
noncomputable def CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.derandomizationSamples
    (X Y : Type*) [Fintype X] [Fintype Y]
    (ε c : ℝ) : ℕ :=
  ⌈Real.log (Fintype.card X * Fintype.card Y) /
    (2 * (c - 1) ^ 2 * ε ^ 2)⌉₊ + 1
