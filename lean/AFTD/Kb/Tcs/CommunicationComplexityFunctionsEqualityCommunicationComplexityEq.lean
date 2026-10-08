import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsEqualityCommunicationComplexityLe
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsEqualityCommunicationComplexityZero
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsEqualityEquality
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsEqualityLeCommunicationComplexity

/-!
# CommunicationComplexity.Functions.Equality.communicationComplexity_eq

Topic: communication   Node: 8b4aee054970

Provenance: formalization of a published result. Source: Exact deterministic complexity of equality, as formalized in TCSlib (`CommunicationComplexity.Functions.Equality.communicationComplexity_eq`). Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncEquality.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Exact deterministic complexity of equality. For a natural number $n$, let $\mathrm{equality}_n$ denote the two-party Boolean
function on $n$-bit strings that returns $\mathtt{true}$ precisely when Alice's input $x
\in \mathrm{BoolInput}(n)$ equals Bob's input $y \in \mathrm{BoolInput}(n)$. Its
deterministic communication complexity, measured in $\bbn_\infty$ as the least
worst-case number of bits exchanged by any deterministic protocol computing it, is
\[
  D(\mathrm{equality}_n) \;=\;
  \begin{cases}
    0 & \text{if } n = 0,\\
    n + 1 & \text{otherwise.}
  \end{cases}
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- The exact deterministic communication complexity of equality on `n`-bit strings is `0` when `n = 0` and `n + 1` otherwise; the lower bound is [RY20, Thm 1.14] and the upper bound is the trivial protocol. Deviation: [RY20] only states the lower bound `≥ n + 1`; here the exact value is given, including the degenerate case `n = 0`. -/
theorem CommunicationComplexity.Functions.Equality.communicationComplexity_eq (n : ℕ) :
    Deterministic.communicationComplexity (equality n) =
      if n = 0 then 0 else n + 1 := by
  split
  · next h => subst h; exact communicationComplexity_zero
  · next h =>
    apply le_antisymm (communicationComplexity_le n)
    exact le_communicationComplexity n (by omega)
