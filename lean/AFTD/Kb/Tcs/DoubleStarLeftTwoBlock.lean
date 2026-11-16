import AFTD.Prelude

/-!
# double_star_left_two_block

Topic: graphs   Node: 9e59fa01cf34

Provenance: helper lemma. step towards two_token_double_star_domination_number_ge

The vertex set consisting of the left centre Sum.inl false together with the a left leaves of the double star S_{a,b}.
-/

/-- The left star block {left centre} ∪ {left leaves} of the double star. -/
def double_star_left_two_block (a b : ℕ) : Finset (Bool ⊕ Fin a ⊕ Fin b) := {Sum.inl false} ∪ Finset.univ.image (fun i : Fin a => Sum.inr (Sum.inl i))
