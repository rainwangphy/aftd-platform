import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeN

/-!
# mkEdge

Topic: quantum   Node: 1d442843cd62

Provenance: formalization of a published result. Source: arXiv:2611.26300

Constructs an edge in a quantum graph connecting vertex $v$ with colour $c_v$ to vertex $u$ with colour $c_u$.
-/

/-- Construct an edge between two vertices with given colours. -/
def mkEdge {N D : ℕ} (v u : Fin N) (cv cu : Fin D) : EdgeN N D := ⟨v, u, cv, cu⟩
