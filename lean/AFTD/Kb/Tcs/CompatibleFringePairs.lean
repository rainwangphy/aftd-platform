import AFTD.Prelude

/-!
# compatible_fringe_pairs

Topic: combinatorics   Node: 1c6378225a05

Provenance: formalization of a published result. Source: arXiv:2611.23338, Appendix B, (B.1)

For each natural number h, compatible_fringe_pairs h is the finset of pairs (E, F) in Finset.powerset (Finset.Ico 0 h) ×ˢ Finset.powerset (Finset.Ico 0 h) of subsets of ℕ such that E.card * 2 > h, F.card * 2 > h, and the pointwise sums satisfy E + E = Finset.Ico 0 (2 * h - 1), E + F = Finset.Ico 0 (2 * h - 1), and F + F = Finset.Ico 0 (2 * h - 1).
-/

open Pointwise in
/-- The finset of compatible fringe pairs (E, F) of subsets of [0, h-1] satisfying the density and sum-filling conditions. -/
def compatible_fringe_pairs (h : ℕ) : Finset (Finset ℕ × Finset ℕ) := ((Finset.powerset (Finset.Ico 0 h)) ×ˢ (Finset.powerset (Finset.Ico 0 h))).filter (fun ⟨E, F⟩ =>
    E.card * 2 > h ∧
    F.card * 2 > h ∧
    E + E = Finset.Ico 0 (2 * h - 1) ∧
    E + F = Finset.Ico 0 (2 * h - 1) ∧
    F + F = Finset.Ico 0 (2 * h - 1))
