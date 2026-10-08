import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsDisjointnessCommunicationComplexityLe
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsDisjointnessDisjointness
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsDisjointnessLeCommunicationComplexity

/-!
# CommunicationComplexity.Functions.Disjointness.communicationComplexity_eq

Topic: communication   Node: 3414d0b9065f

Provenance: formalization of a published result. Source: Deterministic complexity of set disjointness, as formalized in TCSlib (`CommunicationComplexity.Functions.Disjointness.communicationComplexity_eq`). Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncDisjointness.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Deterministic complexity of set disjointness. Let $n \geq 1$, and let $\mathrm{disjointness}(n, \cdot, \cdot)$ denote the two-party
Boolean function that, given subsets $X, Y \subseteq [n]$ held by Alice and Bob
respectively, returns $\mathtt{true}$ exactly when $X \cap Y = \emptyset$. Then the
deterministic communication complexity of this function is exactly $n + 1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open CommunicationComplexity.Rectangle in
open scoped symmDiff in
/-- For `n ≥ 1`, the deterministic communication complexity of disjointness on subsets of `[n]` is exactly `n + 1` [RY20, Thm 1.25]. Deviation: [RY20] states the lower bound `≥ n + 1`; combined with the trivial upper bound this gives the exact value ([Rou16, Cor 4.8] only gives `≥ n`). -/
theorem CommunicationComplexity.Functions.Disjointness.communicationComplexity_eq (n : ℕ) (hn : 1 ≤ n) :
    Deterministic.communicationComplexity (disjointness n) = n + 1 := by
  apply le_antisymm (communicationComplexity_le n)
  exact le_communicationComplexity n hn
