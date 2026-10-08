import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxDisjointAliceOfNe
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxDisjointBobOfNe
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesAux

/-!
# CommunicationComplexity.Deterministic.Protocol.aux_disjoint

Topic: communication   Node: 070c87abf2f9

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.aux_disjoint`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Distinct auxiliary leaf rectangles are disjoint. Let $p$ be a deterministic communication protocol over input types $X$ (Alice) and $Y$
(Bob) producing values of type $\alpha$, and let $A \subseteq X$ and $B \subseteq Y$. If
$R$ and $S$ are two distinct rectangles in the collection of auxiliary leaf rectangles
of $p$ relative to $A$ and $B$, then $R$ and $S$ are disjoint as subsets of $X \times
Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Two distinct leaf rectangles of `p` relative to `A ×ˢ B` are disjoint. **Proof sketch.** Induction on `p`, generalising the constraint. A terminal protocol has a single leaf rectangle, contradicting `R ≠ S`. Step 1: at an Alice node each of `R`, `S` comes from the `false`-child or the `true`-child; if from the same child, apply the induction hypothesis, and if from opposite children, they are disjoint because an input in both would have to send both bits (`aux_disjoint_alice_of_ne`). Step 2: a Bob node is the mirror image with Bob's bit. -/
lemma CommunicationComplexity.Deterministic.Protocol.aux_disjoint (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R S : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) (hS : S ∈ leafRectanglesAux p A B)
    (hne : R ≠ S) : Disjoint R S := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR hS
    exact absurd (hR.trans hS.symm) hne
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    -- Step 1: same side of the split → induction hypothesis; opposite sides → disjoint.
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih false _ _ hR hS
    · exact aux_disjoint_alice_of_ne Bool.false_ne_true hR hS
    · exact aux_disjoint_alice_of_ne Bool.false_ne_true.symm hR hS
    · exact ih true _ _ hR hS
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    -- Step 2: mirror of Step 1 for Bob's split.
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih false _ _ hR hS
    · exact aux_disjoint_bob_of_ne Bool.false_ne_true hR hS
    · exact aux_disjoint_bob_of_ne Bool.false_ne_true.symm hR hS
    · exact ih true _ _ hR hS
