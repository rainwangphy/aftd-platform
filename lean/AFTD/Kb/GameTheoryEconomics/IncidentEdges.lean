import AFTD.Prelude

/-!
# incident_edges

Topic: fair_division   Node: 56594e389707

The relevant items E_i of agent i in a multigraph: the edges incident to i.
-/

/-- The relevant items `E_i` of agent `i` in the multigraph orientation model: the edges incident to vertex `i`. -/
def incident_edges {m n : ℕ} (ends : Fin m → Fin n × Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun e => (ends e).1 = i ∨ (ends e).2 = i
