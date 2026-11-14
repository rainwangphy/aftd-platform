import AFTD.Prelude
import AFTD.Kb.Tcs.RevComp
import AFTD.Kb.Tcs.StringOverlapLen
import AFTD.Kb.Tcs.StringOverlapMerge

/-!
# mgreedy_rc_step

Topic: approximation   Node: cdc848ae2489

Provenance: formalization of a published result. Source: arXiv:2611.16573, Algorithm 1

For cm : Γ → Γ and states st = (S, T), st' : Finset (List Γ) × Finset (List Γ), mgreedy_rc_step cm st st' holds when, with V = S ∪ rev_comp cm '' S, there are x, y ∈ V that are allowed (x = y, or y ≠ x and y ≠ rev_comp cm x), whose string_overlap_len x y is at least string_overlap_len x' y' for every allowed pair x', y' ∈ V, and either x = y and st' = (S \ {x, rev_comp cm x}, insert x T), or x ≠ y and st' = (insert (string_overlap_merge x y) (S \ {x, rev_comp cm x, y, rev_comp cm y}), T). This is one iteration of MGREEDY-RC with arbitrary tie-breaking.
-/

/-- One iteration of the while loop of MGREEDY-RC (Algorithm 1) on the state (S, T), with any tie-breaking among the pairs of maximum overlap. -/
def mgreedy_rc_step {Γ : Type*} [DecidableEq Γ] (cm : Γ → Γ)
    (st st' : Finset (List Γ) × Finset (List Γ)) : Prop :=
  ∃ x ∈ st.1 ∪ st.1.image (rev_comp cm), ∃ y ∈ st.1 ∪ st.1.image (rev_comp cm),
    (x = y ∨ (y ≠ x ∧ y ≠ rev_comp cm x)) ∧
    (∀ x' ∈ st.1 ∪ st.1.image (rev_comp cm), ∀ y' ∈ st.1 ∪ st.1.image (rev_comp cm),
      (x' = y' ∨ (y' ≠ x' ∧ y' ≠ rev_comp cm x')) →
        string_overlap_len x' y' ≤ string_overlap_len x y) ∧
    ((x = y ∧ st' = (st.1 \ {x, rev_comp cm x}, insert x st.2)) ∨
     (x ≠ y ∧ st' = (insert (string_overlap_merge x y)
        (st.1 \ {x, rev_comp cm x, y, rev_comp cm y}), st.2)))
