import AFTD.Prelude

/-!
# CommunicationComplexity.Functions.Indexing.indexing

Topic: communication   Node: 83b44618caa2

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Functions.Indexing.indexing`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/Basic.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Index function on $n$ bits: given Alice's string $x : \mathrm{Fin}\,n \to \mathrm{Bool}$
and Bob's index $i \in \mathrm{Fin}\,n$, it returns Alice's $i$-th bit,
$\mathrm{indexing}_n(x, i) := x_i$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
open scoped BigOperators in
variable (n : ℕ+) in
/-- The Index function on `n` bits: Alice holds a string `x : Fin n → Bool`, Bob holds an index `i : Fin n`, and the answer is Alice's `i`-th bit `x i` [Rou16, §2.4 Definition (Index)]. -/
def CommunicationComplexity.Functions.Indexing.indexing (x : Fin n → Bool) (i : Fin n) : Bool :=
  x i
