import AFTD.Prelude
import AFTD.Kb.Tcs.F4AdjBool

/-!
# f4_graph

Topic: graphs   Node: 89927aaf7936

Provenance: helper lemma. step towards op1917_exists_nonregular_resistance_regular_order_16

The 16-vertex simple graph F(4) constructed in Section 4 of arXiv:2611.21670.
-/

/-- The 16-vertex simple graph F(4) constructed in Section 4 of arXiv:2611.21670. -/
def f4_graph : SimpleGraph (Fin 16) where
  Adj u v := f4_adj_bool u v = true
  symm := ⟨by
    have hsym : ∀ a b : Fin 16, (f4_adj_bool a b == f4_adj_bool b a) = true := by decide
    intro a b h
    have h2 : f4_adj_bool a b = f4_adj_bool b a := eq_of_beq (hsym a b)
    rw [← h2]
    exact h⟩
  loopless := ⟨by
    have hloop : ∀ a : Fin 16, f4_adj_bool a a = false := by decide
    intro a h
    have h2 := hloop a
    rw [h2] at h
    contradiction⟩
