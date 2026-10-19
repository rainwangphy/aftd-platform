import AFTD.Prelude

/-!
# picking_turn

Topic: fair_division   Node: b69620dec267

Provenance: formalization of a published result. Source: arXiv:2610.23040 (On the Convergence of Iterated Round Robin), Sec. 2; also arXiv:2610.23686 Sec. 2

One turn of a picking-sequence mechanism: the active agent i receives the first good of its reported ranking l (best first) that is not yet allocated; the state is the partial allocation together with the set of allocated goods.
-/

/-- One turn of a picking-sequence mechanism: the active agent `i` receives the first good of its reported ranking `l` (best first) not yet allocated. The state is the partial allocation and the set of goods already allocated. -/
def picking_turn {N G : Type*} [DecidableEq N] [DecidableEq G] (l : List G) (i : N)
    (st : (N → Finset G) × Finset G) : (N → Finset G) × Finset G :=
  match l.find? (fun g => decide (g ∉ st.2)) with
  | some g => (Function.update st.1 i (insert g (st.1 i)), insert g st.2)
  | none => st
