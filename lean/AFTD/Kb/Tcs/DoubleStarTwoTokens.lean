import AFTD.Prelude

/-!
# double_star_two_tokens

Topic: graphs   Node: 2725483f5664

Provenance: helper lemma. step towards two_token_double_star_domination_number_ge

The vertex type of the 2-token graph of the double star S_{a,b}: the 2-element subsets of Bool ⊕ Fin a ⊕ Fin b.
-/

/-- Abbreviation for the vertex type of `token_graph (double_star_graph a b) 2`. -/
abbrev double_star_two_tokens (a b : ℕ) : Type := {s : Finset (Bool ⊕ Fin a ⊕ Fin b) // s.card = 2}
