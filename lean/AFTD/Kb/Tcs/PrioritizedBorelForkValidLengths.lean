import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelForkValid

/-!
# prioritized_borel_fork_valid_lengths

Topic: automata   Node: 37220b047223

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2, smallest lower-bound arena; three-move fork obstruction

In each compatible block history the visible and hidden histories have equal length.
-/

theorem prioritized_borel_fork_valid_lengths {color : List Bool → List Bool → Bool} {u h : List Bool}
    (hv : PrioritizedBorelForkValid color u h) : u.length = h.length := by
  induction hv with
  | root => rfl
  | stay bit hv ih => simp [ih]
  | exit hv ih => simp [ih]
