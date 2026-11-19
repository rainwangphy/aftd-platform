import AFTD.Prelude
import AFTD.Kb.Tcs.RetainedLineMsfWeight

/-!
# retained_line_expected_msf

Topic: algorithms   Node: 91e43261434e

Provenance: helper lemma. OP-815, proposed here; compares independent edge retention on the line with classical random spanning-tree results.

The expectation of the minimum spanning forest weight on n linearly arranged vertices when every possible edge is independently retained with probability q, for 0 ≤ q ≤ 1.
-/

noncomputable def retained_line_expected_msf (n : ℕ) (q : ℝ) : ℝ := by
  classical
  exact ∑ G : SimpleGraph (Fin n),
    q ^ G.edgeFinset.card * (1 - q) ^ (Nat.choose n 2 - G.edgeFinset.card) *
      retained_line_msf_weight G
