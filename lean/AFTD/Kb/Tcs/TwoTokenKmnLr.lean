import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmnLefts

/-!
# two_token_kmn_lr

Topic: graphs   Node: e44ddd733c7b

Provenance: helper lemma. step towards two_token_kmn_domination_number

A vertex of F_2(K_{m,n}) is of type LR when it contains exactly one left and one right vertex.
-/

/-- The LR class: 2-subsets with one element in each part. -/
abbrev two_token_kmn_lr {m n : ℕ} (v : {s : Finset (Fin m ⊕ Fin n) // s.card = 2}) : Prop := (two_token_kmn_lefts v).card = 1
