import AFTD.Prelude
import AFTD.Kb.Tcs.IsDistanceHereditary

/-!
# distance_hereditary_subsingleton

Topic: graphs   Node: 91a6b0421caa

Provenance: helper lemma. folklore

Every graph on at most one vertex is distance-hereditary.
-/

/-- Any graph on at most one vertex is distance-hereditary. -/
theorem distance_hereditary_subsingleton {α : Type*} [Subsingleton α] (G : SimpleGraph α) :
    is_distance_hereditary G := by
  intro s u v _
  have hu : u = v := Subsingleton.elim u v
  subst hu
  rw [SimpleGraph.dist_self, SimpleGraph.dist_self]
