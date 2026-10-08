import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityBoolInput

/-!
# CommunicationComplexity.Functions.Equality.equality

Topic: communication   Node: a8ac144ed6a6

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Functions.Equality.equality`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncEquality.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a natural number $n$, \texttt{CommunicationComplexity.Functions.Equality.equality}
is the Boolean function
$\mathrm{equality}_n : \mathrm{BoolInput}\,n \times \mathrm{BoolInput}\,n \to \mathrm{Bool}$
that returns \texttt{true} if and only if Alice's input $x$ equals Bob's input $y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- The equality function on `n`-bit strings: `equality n x y` is `true` if and only if `x = y` [RY20, Ch. 1, eq. (1.1)]. -/
def CommunicationComplexity.Functions.Equality.equality (n : ℕ) (x y : BoolInput n) : Bool :=
  decide (x = y)
