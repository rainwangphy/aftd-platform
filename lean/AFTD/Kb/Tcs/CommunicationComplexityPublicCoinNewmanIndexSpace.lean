import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolDerandomizationSamples

/-!
# CommunicationComplexity.PublicCoin.newmanIndexSpace

Topic: communication   Node: e48b13fac7ef

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.newmanIndexSpace`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Newman.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given finite input types $X$ and $Y$ and parameters $\varepsilon, c \in \mathbb{R}$,
the \emph{Newman index space} is $\mathrm{Fin}(\mathtt{derandomizationSamples}\;X\;Y\;\varepsilon\;c)$,
i.e.\ the finite type indexing the table of random seeds that Alice samples from in the Newman
reduction.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- The index space of the Newman reduction: the finite type `Fin (derandomizationSamples X Y ε c)` of indices into the table of `t` good seeds, from which Alice samples uniformly and whose element she sends to Bob. [RY20, Thm 3.5 proof] (Alice sends the index of one of the `t` good strings). -/
noncomputable abbrev CommunicationComplexity.PublicCoin.newmanIndexSpace
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :=
  Fin (FiniteMessage.Protocol.derandomizationSamples X Y ε c)
