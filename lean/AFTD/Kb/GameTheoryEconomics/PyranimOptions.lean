import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PyranimRemove

/-!
# pyranim_options

Topic: combinatorial_games   Node: 710d68a5c886

Provenance: formalization of a published result. Source: arXiv:2611.16153 Def. 1.2

For a position X : Finset (ℕ × ℕ), pyranim_options X is the finite set of successor positions obtained by applying pyranim_remove X c for all visible chips c ∈ X that do not have both immediate upper chips in X.
-/

/-- The set of legal successor positions obtained by removing each visible chip from X. -/
def pyranim_options (X : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) := (X.filter (fun c => ¬ ((c.1 - 1, c.2) ∈ X ∧ (c.1, c.2 + 1) ∈ X))).image (pyranim_remove X)
