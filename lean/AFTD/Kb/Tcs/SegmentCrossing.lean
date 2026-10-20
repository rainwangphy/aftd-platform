import AFTD.Prelude

/-!
# segment_crossing

Topic: combinatorics   Node: 49cf10b0caed

Provenance: formalization of a published result. Source: arXiv:2610.23130 Sec. 1

Two line segments in the plane, represented as unordered pairs of endpoints in Sym2 (ℝ × ℝ), cross if the intersection of their relative interiors (open segments) is nonempty.
-/

/-- Predicate that two line segments in ℝ² intersect in their relative interiors. -/
def segment_crossing (e₁ e₂ : Sym2 (ℝ × ℝ)) : Prop := ((Sym2.lift ⟨fun u v => openSegment ℝ u v, fun u v => openSegment_symm (𝕜 := ℝ) u v⟩ e₁) ∩
   (Sym2.lift ⟨fun u v => openSegment ℝ u v, fun u v => openSegment_symm (𝕜 := ℝ) u v⟩ e₂)).Nonempty
