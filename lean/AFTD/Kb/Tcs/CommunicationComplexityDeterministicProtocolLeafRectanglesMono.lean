import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComputes
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolAuxMono
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonochromatic

/-!
# CommunicationComplexity.Deterministic.Protocol.leafRectangles_mono

Topic: communication   Node: f8bb8cb999ce

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.leafRectangles_mono`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Leaf rectangles of a protocol are monochromatic. Let $p$ be a deterministic two-party communication protocol over input types $X$ and $Y$
with output type $\alpha$, and let $g : X \to Y \to \alpha$ be a function that $p$
computes, meaning that running $p$ on any pair of inputs $(x, y)$ returns $g\,x\,y$.
Then every leaf rectangle $R$ of $p$ is monochromatic for $g$: the value $g\,x\,y$ is
the same for all $(x, y) \in R$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- If `p` computes `g`, then every leaf rectangle of `p` is monochromatic for `g`, i.e. `g` takes a single value on it [RY20, Lemma 1.6]: two inputs in the same leaf rectangle reach the same leaf, hence produce the same output. -/
lemma CommunicationComplexity.Deterministic.Protocol.leafRectangles_mono (p : Protocol X Y α)
    (g : X → Y → α) (h_comp : Computes p g)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : Rectangle.IsMonochromatic R g := by
  intro x x' y y' hxy hxy'
  have := aux_mono p Set.univ Set.univ R hR x x' y y' hxy hxy'
  simp only [Computes, funext_iff] at h_comp
  rw [← h_comp x y, ← h_comp x' y']; exact this
