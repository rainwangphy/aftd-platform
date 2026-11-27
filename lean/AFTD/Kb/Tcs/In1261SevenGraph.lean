import AFTD.Prelude
import AFTD.Kb.Tcs.In1261SevenForbiddenOrdered

/-!
# in1261_seven_graph

Topic: graphs   Node: 9b9701c4d626

Provenance: helper lemma. OP-1957: seven-by-seven boundary control, experiment 43349, arXiv:2611.22690.

The symmetric graph on 28 vertices whose unequal ordered endpoints avoid the displayed forbidden pairs.
-/

def in1261_seven_graph : SimpleGraph (Fin 28) where
  Adj := fun u v => u ≠ v ∧ ¬ in1261_seven_forbidden_ordered (min u.val v.val) (max u.val v.val)
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm,by simpa [min_comm,max_comm] using h.2⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩
