import AFTD.Prelude

/-!
# rectilinear_crossing_number

Topic: combinatorics   Node: 9163b1849ff2

Provenance: formalization of a published result. Source: arXiv:2610.38658, Section 4

For a finite set P of points in the plane ℝ × ℝ, the rectilinear crossing number of P is the number of unordered pairs of disjoint 2-element subsets {e₁, e₂} of P whose open line segments have nonempty intersection.
-/

/-- Rectilinear crossing number of a finite point set P in ℝ × ℝ. -/
noncomputable def rectilinear_crossing_number (P : Finset (ℝ × ℝ)) : ℕ := open Classical in (((P.powersetCard 2).powersetCard 2).filter (fun (pair : Finset (Finset (ℝ × ℝ))) => ∃ e₁ ∈ pair, ∃ e₂ ∈ pair, e₁ ≠ e₂ ∧ Disjoint e₁ e₂ ∧ ∃ u₁ ∈ e₁, ∃ v₁ ∈ e₁, ∃ u₂ ∈ e₂, ∃ v₂ ∈ e₂, u₁ ≠ v₁ ∧ u₂ ≠ v₂ ∧ (openSegment ℝ u₁ v₁ ∩ openSegment ℝ u₂ v₂).Nonempty)).card
