import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHypercube

/-!
# simple_graph_hypercube_coordinate_flip

Topic: graphs   Node: 70a57e6edeaa

Provenance: helper lemma. step towards op_300_leap_group_prism_and_hypercube

The permutation of the vertices of the hypercube Q_n that inverts a single coordinate i.
-/

/-- The coordinate flip of the hypercube as an involutive permutation of the vertices. -/
def simple_graph_hypercube_coordinate_flip (n : ℕ) (i : Fin n) : Equiv.Perm (Fin n → Bool) := Function.Involutive.toPerm (fun x : Fin n → Bool => Function.update x i (!x i)) (by
      intro x
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Function.update, hj])
