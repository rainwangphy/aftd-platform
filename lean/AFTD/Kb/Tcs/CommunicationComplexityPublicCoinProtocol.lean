import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol

/-!
# CommunicationComplexity.PublicCoin.Protocol

Topic: communication   Node: 42a2ac3b597f

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.Protocol`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinBasic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A public-coin protocol over shared randomness $\Omega$, with Alice's private input
in $X$ and Bob's in $Y$ producing an output in $\alpha$, is a deterministic protocol
whose combined input types are $\Omega \times X$ (for Alice) and $\Omega \times Y$
(for Bob).  In other words, both players observe the same random string $\omega \in \Omega$
alongside their private inputs.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- A public-coin protocol with randomness `Ω`, inputs `X`, `Y` and outputs `α`: a deterministic protocol where both Alice and Bob see the shared random string `ω : Ω` in addition to their own inputs, so Alice's input is `(ω, x)` and Bob's is `(ω, y)` [RY20, Ch. 3, §Variants of Randomized Protocols: public coins]. -/
abbrev CommunicationComplexity.PublicCoin.Protocol (Ω : Type*) (X Y α : Type*) :=
  Deterministic.Protocol (Ω × X) (Ω × Y) α
