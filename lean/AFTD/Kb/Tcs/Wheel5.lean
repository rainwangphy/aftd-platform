import AFTD.Prelude
import AFTD.Kb.Tcs.Wheel5Vert

/-!
# wheel5

Topic: graphs   Node: ee0833b3f53c

Provenance: formalization of a published result. Source: arXiv:2611.03236 Sec. 3

The 6-vertex wheel graph W₅ with center u and rim cycle v 0, ..., v 4.
-/

/-- The 6-vertex wheel graph W₅ with center u and rim 5-cycle. -/
def wheel5 : SimpleGraph Wheel5Vert := {
  Adj := fun x y =>
    match x, y with
    | .u, .v _ => True
    | .v _, .u => True
    | .v i, .v j => (SimpleGraph.cycleGraph 5).Adj i j
    | .u, .u => False
  symm := ⟨by
    rintro (_ | i) (_ | j) h
    · exact False.elim h
    · trivial
    · trivial
    · exact (SimpleGraph.cycleGraph 5).adj_symm h⟩
  loopless := ⟨by
    rintro (_ | i) h
    · exact False.elim h
    · exact (SimpleGraph.cycleGraph 5).loopless.irrefl i h⟩
}
