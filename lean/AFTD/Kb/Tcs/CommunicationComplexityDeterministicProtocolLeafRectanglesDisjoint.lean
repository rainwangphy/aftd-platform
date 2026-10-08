import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxDisjoint

/-!
# CommunicationComplexity.Deterministic.Protocol.leafRectangles_disjoint

Topic: communication   Node: 2206f42b148f

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.leafRectangles_disjoint`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Distinct leaf rectangles are disjoint. Let $p$ be a deterministic two-party communication protocol over input types $X$ and $Y$
producing values in $\alpha$, and let $R$ and $S$ be two of its leaf rectangles, that
is, two of the input rectangles induced by the leaves of $p$ over $X \times Y$. If $R
\neq S$, then $R$ and $S$ are disjoint as subsets of $X \times Y$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- Two distinct leaf rectangles of a protocol are disjoint [RY20, Lemma 1.6] (also [Rou16, Lemma 4.1, Lemma 4.2]). -/
lemma CommunicationComplexity.Deterministic.Protocol.leafRectangles_disjoint (p : Protocol X Y α)
    (R S : Set (X × Y)) (hR : R ∈ leafRectangles p) (hS : S ∈ leafRectangles p)
    (hne : R ≠ S) : Disjoint R S :=
  aux_disjoint p Set.univ Set.univ R S hR hS hne
