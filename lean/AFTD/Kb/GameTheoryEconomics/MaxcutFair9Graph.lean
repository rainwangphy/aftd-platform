import AFTD.Prelude

/-!
# maxcut_fair9_graph

Topic: equilibria   Node: f1c2f8e84ac2

Provenance: helper lemma. Nine-vertex finite obstruction to fair Nash selection in the OP-85 strong-equilibrium campaign, discovered in experiment 12959 and independently checked in 12961, 12964, and 12973.

The explicit nine-vertex simple graph used to obstruct fair Nash selection.
-/

def maxcut_fair9_graph : SimpleGraph (Fin 9) :=
  SimpleGraph.fromRel (fun (u v : Fin 9) => (u.val, v.val) ∈
    [(0,1),(0,2),(0,3),(0,5),(0,7),(1,3),(1,6),(1,7),(1,8),
     (2,3),(2,6),(2,7),(2,8),(3,4),(3,5),(3,6),(3,8),
     (4,5),(4,7),(4,8),(5,6),(5,7),(5,8),(6,7),(7,8)])
