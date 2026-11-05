import AFTD.Prelude
import AFTD.Kb.Tcs.ColoredRootedTree
import AFTD.Kb.Tcs.IntervalFamily
import AFTD.Kb.Tcs.NearestAncestorOfColor

/-!
# is_correct_interval_family

Topic: data_structures   Node: 87961a026d3c

Provenance: formalization of a published result. Source: arXiv:2611.03620 Definition 2.2

An interval family is correct if for every vertex x and color c different from that of x, whenever x has a nearest proper ancestor u of color c, the innermost interval of color c containing id(x) is owned by u.
-/

/-- Correctness of an interval family. -/
def is_correct_interval_family {T : ColoredRootedTree} {R : ℕ} (F : IntervalFamily T R) : Prop := ∀ (x : T.V) (c : Fin 4) (u : T.V),
    c ≠ T.color x →
    nearest_ancestor_of_color T x c u →
    ∃ i : F.ι,
      T.color (F.owner i) = c ∧
      F.owner i = u ∧
      F.id x ∈ F.interval i ∧
      ∀ j : F.ι, T.color (F.owner j) = c → F.id x ∈ F.interval j → F.interval i ⊆ F.interval j
