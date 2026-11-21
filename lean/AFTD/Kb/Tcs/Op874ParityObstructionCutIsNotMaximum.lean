import AFTD.Prelude

/-!
# op874_parity_obstruction_cut_is_not_maximum

Topic: graphs   Node: f421e408eb19

Provenance: helper lemma. OP-874: cut-score check for the eight-vertex parity obstruction, experiment 37131

For the displayed eight-vertex matching and factor, the locally maximal obstruction cut has four crossing factor edges, while the largest matching-constant cut has six.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem op874_parity_obstruction_cut_is_not_maximum :
    let b : Fin 8 → Bool := ![false,false,true,true,false,false,true,true]
    let edges : List (Fin 8 × Fin 8) := [(0,3),(3,7),(7,0),(1,5),(5,4),(4,2),(2,6),(6,1)]
    let score := fun c : Fin 8 → Bool => (edges.filter fun p => c p.1 != c p.2).length
    score b = 4 ∧
    (∀ c : Fin 8 → Bool, c 0 = c 5 → c 1 = c 4 → c 2 = c 7 → c 3 = c 6 → score c ≤ 6) ∧
    ∃ c : Fin 8 → Bool, c 0 = c 5 ∧ c 1 = c 4 ∧ c 2 = c 7 ∧ c 3 = c 6 ∧ score c = 6 := by
  decide
