import AFTD.Prelude

/-!
# is_graph_valuation

Topic: fair_division   Node: 3ac4d01d51d8

In the graph model each agent values only the edges incident to her: v_i(X) = v_i(X ∩ E_i).
-/

/-- Every agent values only the edges incident to her: `v i X = v i (X ∩ E_i)`. -/
def is_graph_valuation {m n : ℕ} (ends : Fin m → Fin n × Fin n)
    (v : Fin n → Finset (Fin m) → ℝ) : Prop :=
  ∀ i S, v i S = v i (S.filter fun e => (ends e).1 = i ∨ (ends e).2 = i)
