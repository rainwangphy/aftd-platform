import AFTD.Prelude
import AFTD.Kb.Tcs.IntervalFamily
import AFTD.Kb.Tcs.ColoredRootedTree

/-!
# interval_family_member_depth

Topic: data_structures   Node: 916c70b57464

Provenance: formalization of a published result. Source: arXiv:2611.03620 (Adjacency Labeling Schemes of Size log n + O(log log* n) for Graphs of Bounded Treewidth), Definition 2.2 (depth of a member of F).

The depth of a member I of an interval family: the number of members of the same color as I (the color of the owner) whose interval contains the interval of I, I itself included.
-/

noncomputable def interval_family_member_depth {T : ColoredRootedTree} {R : ℕ} (F : IntervalFamily T R)
    (i : F.ι) : ℕ :=
  Nat.card {j : F.ι // T.color (F.owner j) = T.color (F.owner i) ∧ F.interval i ⊆ F.interval j}
