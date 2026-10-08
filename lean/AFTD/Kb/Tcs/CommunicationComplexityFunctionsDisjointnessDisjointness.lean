import AFTD.Prelude

/-!
# CommunicationComplexity.Functions.Disjointness.disjointness

Topic: communication   Node: 76866ced0c79

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Functions.Disjointness.disjointness`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncDisjointness.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For $n \in \mathbb{N}$ and subsets $X, Y \subseteq [n]$, $\mathrm{disjointness}(n, X, Y)$
is the Boolean function that returns $\mathtt{true}$ if and only if $X$ and $Y$ are
disjoint, i.e.\ $X \cap Y = \emptyset$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open scoped symmDiff in
/-- The set-disjointness function on subsets of `[n]`: `disjointness n X Y` is `true` if and only if `X ∩ Y = ∅` [RY20, Ch. 1, eq. (1.2)]. -/
noncomputable def CommunicationComplexity.Functions.Disjointness.disjointness (n : ℕ) (X Y : Set (Fin n)) : Bool :=
  by
    classical
    exact decide (Disjoint X Y)
