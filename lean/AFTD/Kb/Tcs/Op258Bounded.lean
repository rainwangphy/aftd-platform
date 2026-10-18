import AFTD.Prelude

/-!
# op_258_bounded

Topic: combinatorics   Node: 3ce2b7ab8df6

Provenance: helper lemma. step towards op_258_triangle_forcing_implies_decay_ramsey

A colouring c of the edges of the complete graph K_n is a-bounded if for every colour i the number of edges of colour i is at most a i * C(n,2).
-/

/-- a-bounded edge colouring of the complete graph on `Fin n`: every colour class has size at most the `a i` fraction of the `C(n,2)` edges. -/
def op_258_bounded (a : ℕ+ → ℝ) (n : ℕ) (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) : Prop := ∀ i : ℕ+, ((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e => c e = i)).card ≤ a i * (n.choose 2 : ℝ)
