import AFTD.Prelude

/-!
# CommunicationComplexity.Functions.Disjointness.foolingSet

Topic: communication   Node: 9dd57507d75d

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Functions.Disjointness.foolingSet`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncDisjointness.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The candidate fooling set for disjointness is the collection of all pairs
$(X, X^c)$ where $X \subseteq [n]$, i.e.\ $\mathrm{foolingSet}(n) = \{(X, Y) \mid Y = X^c\}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open scoped symmDiff in
/-- The fooling set for disjointness: the set of all pairs `(X, Xᶜ)` of a subset of `[n]` and its complement [RY20, Ch. 1, §Using Fooling Sets]. -/
def CommunicationComplexity.Functions.Disjointness.foolingSet (n : ℕ) : Set (Set (Fin n) × Set (Fin n)) :=
  {p | p.2 = p.1ᶜ}
