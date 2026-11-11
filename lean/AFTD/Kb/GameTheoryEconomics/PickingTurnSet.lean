import AFTD.Prelude

/-!
# picking_turn_set

Topic: fair_division   Node: 40655cef50ac

Provenance: helper lemma. step towards independent_rank_trajectories_sequential_draft

The set T_i of turns at which agent i acts in a picking sequence of length m: the positions t : Fin m whose actor is i.
-/

/-- The turn set of agent i: the positions t < m at which agent i acts. -/
def picking_turn_set {n m : ℕ} (seq : List (Fin n)) (hlen : seq.length = m) (i : Fin n) : Finset (Fin m) := Finset.univ.filter (fun t : Fin m => seq.get (Fin.cast hlen.symm t) = i)
