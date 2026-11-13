import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PyranimFullPyramid
import AFTD.Kb.GameTheoryEconomics.PyranimIsOrderIdeal

/-!
# pyranim_stable_positions

Topic: combinatorial_games   Node: 6cbc9f9c301f

Provenance: formalization of a published result. Source: arXiv:2611.16153 Def. 1.1

For a natural number n, pyranim_stable_positions n is the finite set of all subsets X of pyranim_full_pyramid n that satisfy the order ideal predicate pyranim_is_order_ideal X.
-/

/-- The finite set of all stable positions of an n-tier Pyranim game. -/
noncomputable def pyranim_stable_positions (n : ℕ) : Finset (Finset (ℕ × ℕ)) := @Finset.filter (Finset (ℕ × ℕ)) pyranim_is_order_ideal (fun _ => Classical.propDecidable _) (pyranim_full_pyramid n).powerset
