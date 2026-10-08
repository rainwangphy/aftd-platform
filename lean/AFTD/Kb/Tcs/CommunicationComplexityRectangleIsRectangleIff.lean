import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle

/-!
# CommunicationComplexity.Rectangle.IsRectangle_iff

Topic: communication   Node: c27d51ed64ad

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Rectangle.IsRectangle_iff`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rectangle.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cross characterization of combinatorial rectangles. A subset $R \subseteq X \times Y$ is a rectangle — that is, $R = A \times B$ for some $A
\subseteq X$ and $B \subseteq Y$ — if and only if it is closed under crossing: for all
$x, x' \in X$ and $y, y' \in Y$, whenever $(x, y) \in R$ and $(x', y') \in R$, both
mixed pairs $(x', y)$ and $(x, y')$ also lie in $R$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {X Y α : Type*} in
/-- A set `R ⊆ X × Y` is a rectangle if and only if it has the cross property: whenever `(x, y)` and `(x', y')` lie in `R`, so do the mixed pairs `(x', y)` and `(x, y')`. [RY20, Lemma 1.5]. -/
theorem CommunicationComplexity.Rectangle.IsRectangle_iff (R : Set (X × Y)) :
    IsRectangle R ↔ ∀ x x' y y', (x, y) ∈ R → (x', y') ∈ R → (x', y) ∈ R ∧ (x, y') ∈ R := by
  constructor
  · rintro ⟨A, B, rfl⟩ x x' y y' ⟨hx, hy⟩ ⟨hx', hy'⟩
    exact ⟨⟨hx', hy⟩, ⟨hx, hy'⟩⟩
  · intro h
    refine ⟨Prod.fst '' R, Prod.snd '' R, ?_⟩
    ext ⟨x, y⟩
    simp only [Set.mem_prod, Set.mem_image, Prod.exists]
    constructor
    · intro hxy
      exact ⟨⟨x, y, hxy, rfl⟩, ⟨x, y, hxy, rfl⟩⟩
    · rintro ⟨⟨x', y', hx'y', rfl⟩, ⟨x'', y'', hx''y'', rfl⟩⟩
      exact (h _ _ _ _ hx'y' hx''y'').2
