import AFTD.Prelude

/-!
# digraph_arborescence_count_at_through

Topic: graphs   Node: 95262d98c0b3

Provenance: helper lemma. step towards tournament_not_near_regular_exists_improving_tournament

through_r(D, a → b): the number of spanning arborescences of D directed towards the root r that use the arc a → b, i.e. whose successor map sends a to b.
-/

/-- Number of arborescences of D directed towards r whose successor map sends a to b. -/
def digraph_arborescence_count_at_through {n : ℕ} (D : Digraph (Fin n)) [DecidableRel D.Adj] (r a b : Fin n) : ℕ := (Finset.univ.filter (fun p : Fin n → Fin n =>
    p r = r ∧ (∀ w, w ≠ r → D.Adj w (p w)) ∧ (∀ w, p^[n] w = r) ∧ p a = b)).card
