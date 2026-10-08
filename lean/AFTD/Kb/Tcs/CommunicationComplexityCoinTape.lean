import AFTD.Prelude

/-!
# CommunicationComplexity.CoinTape

Topic: communication   Node: 409ef418b46c

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.CoinTape`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/CoinTape.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\texttt{CoinTape}(n)$ is the type $\mathrm{Fin}\,n \to \mathrm{Bool}$, i.e.\ the set of
all binary strings of length $n$, representing the $2^n$ possible outcomes of $n$
independent fair coin flips.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A coin tape of length `n`: a sequence of `n` bits, one per fair coin flip, i.e. a function `Fin n → Bool`. This is the random string that a randomized protocol has access to beyond its inputs [RY20, Ch. 3, Definition (randomized protocol)]; here it consists of `n` fair bits, uniformly distributed via `coinTapeMeasure`. -/
abbrev CommunicationComplexity.CoinTape (n : ℕ) := Fin n → Bool
