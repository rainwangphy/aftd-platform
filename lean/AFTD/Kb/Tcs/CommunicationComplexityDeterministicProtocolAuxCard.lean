import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxCardStep
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesAux

/-!
# CommunicationComplexity.Deterministic.Protocol.aux_card

Topic: communication   Node: 3a9b428e2c56

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.aux_card`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Leaf rectangle count bounded by two to the complexity. Let $p$ be a deterministic two-party communication protocol with input types $X$ (Alice)
and $Y$ (Bob), and let $A \subseteq X$ and $B \subseteq Y$. Then the number of distinct
rectangles among the auxiliary leaf rectangles of $p$ relative to the constraint $A
\times B$ is at most $2^{c}$, where $c$ is the communication complexity of $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- A protocol of complexity `c` has at most `2 ^ c` leaf rectangles relative to any constraint `A ×ˢ B`. **Proof sketch.** Induction on `p`. A terminal protocol has one leaf rectangle and complexity `0`. Step 1: at an Alice node the leaf rectangles are the union of the two children's, each bounded by the induction hypothesis, and `aux_card_step` gives `2 ^ c₀ + 2 ^ c₁ ≤ 2 ^ (1 + max c₀ c₁)`, the bound for the node. Step 2: a Bob node is identical. -/
lemma CommunicationComplexity.Deterministic.Protocol.aux_card (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    Set.ncard (leafRectanglesAux p A B) ≤ 2 ^ p.complexity := by
  induction p generalizing A B with
  | output _ =>
    simp [leafRectanglesAux, complexity]
  | alice f P ih =>
    -- Step 1: the two children contribute at most `2^c₀ + 2^c₁ ≤ 2^(1 + max c₀ c₁)`.
    simp only [leafRectanglesAux, complexity]
    exact aux_card_step (ih false _ _) (ih true _ _)
  | bob f P ih =>
    -- Step 2: mirror of Step 1 for Bob's split.
    simp only [leafRectanglesAux, complexity]
    exact aux_card_step (ih false _ _) (ih true _ _)
