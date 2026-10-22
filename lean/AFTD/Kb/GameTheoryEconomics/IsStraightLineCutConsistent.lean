import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StraightLine

/-!
# is_straight_line_cut_consistent

Topic: fair_division   Node: 9bf075fd275a

Provenance: original. Related work: arXiv:2610.27956 Section 1.1

Given a finite set P of points in ℝ × ℝ, a finite set L of straight lines (StraightLine), a natural number k, and an allocation function α : (ℝ × ℝ) → Fin k, is_straight_line_cut_consistent P L α asserts that there exists a function s : StraightLine → (ℝ × ℝ) → Bool such that for every line ℓ ∈ L and point p ∈ P, if 0 < ℓ.cut p then s ℓ p = true and if ℓ.cut p < 0 then s ℓ p = false, and for all points p, q ∈ P, if s ℓ p = s ℓ q for all ℓ ∈ L then α p = α q.
-/

/-- An allocation α of a finite set of points P to k agents is consistent with a finite set of straight lines L if points directly on cuts can be assigned boolean sides such that any two points sharing the same side vector across all lines in L receive the same agent. -/
def is_straight_line_cut_consistent (P : Finset (ℝ × ℝ)) (L : Finset StraightLine) {k : ℕ}
    (α : (ℝ × ℝ) → Fin k) : Prop := ∃ s : StraightLine → (ℝ × ℝ) → Bool,
    (∀ ℓ ∈ L, ∀ p ∈ P, (0 < ℓ.cut p → s ℓ p = true) ∧ (ℓ.cut p < 0 → s ℓ p = false)) ∧
    (∀ p ∈ P, ∀ q ∈ P, (∀ ℓ ∈ L, s ℓ p = s ℓ q) → α p = α q)
