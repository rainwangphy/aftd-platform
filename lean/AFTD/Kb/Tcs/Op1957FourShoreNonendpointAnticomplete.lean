import AFTD.Prelude

/-!
# op1957_four_shore_nonendpoint_anticomplete

Topic: graphs   Node: 1691c91c806f

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Four shore nonendpoint anticomplete.
-/

set_option maxHeartbeats 2000000

theorem op1957_four_shore_nonendpoint_anticomplete
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F : Fin 4 → Finset V) (x y : V)
    (hcross : ∀ i l : Fin 4, i ≠ l → ∀ a ∈ F i, ∀ b ∈ F l, G.Adj a b →
      (i=0 ∧ l=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ l=0 ∧ a=y ∧ b=x))
    (j : Fin 4) (v : V) (hv : v ∈ F j)
    (hx : j=0 → v ≠ x) (hy : j=1 → v ≠ y) :
    ∀ i : Fin 4, i ≠ j → ∀ w ∈ F i, ¬ G.Adj v w := by
  intro i hij w hw hadj
  rcases hcross j i (Ne.symm hij) v hv w hw hadj with h | h
  · exact (hx h.1) h.2.2.1
  · exact (hy h.1) h.2.2.1
