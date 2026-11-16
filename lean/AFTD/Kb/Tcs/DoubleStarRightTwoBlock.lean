import AFTD.Prelude

/-!
# double_star_right_two_block

Topic: graphs   Node: 8ac4b64ff9ca

Provenance: helper lemma. step towards two_token_double_star_domination_number_ge

The vertex set consisting of the right centre Sum.inl true together with the b right leaves of the double star S_{a,b}.
-/

/-- The right star block {right centre} ∪ {right leaves} of the double star. -/
def double_star_right_two_block (a b : ℕ) : Finset (Bool ⊕ Fin a ⊕ Fin b) := {Sum.inl true} ∪ Finset.univ.image (fun j : Fin b => Sum.inr (Sum.inr j))
