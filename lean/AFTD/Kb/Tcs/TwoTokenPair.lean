import AFTD.Prelude

/-!
# two_token_pair

Topic: graphs   Node: 3d7eb2aac086

Provenance: helper lemma. step towards two_token_double_star_domination_number_ge

For distinct vertices x and y of V, the pair {x, y}, regarded as a vertex of the 2-token graph.
-/

/-- The two-element set {x, y} as a vertex of a 2-token graph. -/
def two_token_pair {V : Type*} [DecidableEq V] (x y : V) (h : x ≠ y) : {s : Finset V // s.card = 2} := ⟨{x, y}, by simpa using Finset.card_pair h⟩
