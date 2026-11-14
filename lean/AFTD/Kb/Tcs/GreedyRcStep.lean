import AFTD.Prelude
import AFTD.Kb.Tcs.RevComp
import AFTD.Kb.Tcs.StringOverlapLen
import AFTD.Kb.Tcs.StringOverlapMerge

/-!
# greedy_rc_step

Topic: approximation   Node: 3f77b267aa63

Provenance: formalization of a published result. Source: arXiv:2611.16573, Algorithm 2

For cm : Γ → Γ and S, S' : Finset (List Γ), greedy_rc_step cm S S' holds when S has more than one element and, with V = S ∪ rev_comp cm '' S, there are x, y ∈ V with y ≠ x and y ≠ rev_comp cm x whose string_overlap_len x y is at least string_overlap_len x' y' for every pair x', y' ∈ V with y' ≠ x' and y' ≠ rev_comp cm x', and S' = insert (string_overlap_merge x y) (S \ {x, rev_comp cm x, y, rev_comp cm y}). This is one iteration of GREEDY-RC with arbitrary tie-breaking.
-/

/-- One iteration of the while loop of GREEDY-RC (Algorithm 2), with any tie-breaking. -/
def greedy_rc_step {Γ : Type*} [DecidableEq Γ] (cm : Γ → Γ)
    (S S' : Finset (List Γ)) : Prop :=
  1 < S.card ∧
  ∃ x ∈ S ∪ S.image (rev_comp cm), ∃ y ∈ S ∪ S.image (rev_comp cm),
    (y ≠ x ∧ y ≠ rev_comp cm x) ∧
    (∀ x' ∈ S ∪ S.image (rev_comp cm), ∀ y' ∈ S ∪ S.image (rev_comp cm),
      (y' ≠ x' ∧ y' ≠ rev_comp cm x') →
        string_overlap_len x' y' ≤ string_overlap_len x y) ∧
    S' = insert (string_overlap_merge x y) (S \ {x, rev_comp cm x, y, rev_comp cm y})
