import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmnLefts

/-!
# two_token_kmn_ll

Topic: graphs   Node: 36750f858545

Provenance: helper lemma. step towards two_token_kmn_domination_number

A vertex of F_2(K_{m,n}) is of type LL when both of its elements are left vertices.
-/

/-- The LL class: 2-subsets contained in the left part. -/
abbrev two_token_kmn_ll {m n : ℕ} (v : {s : Finset (Fin m ⊕ Fin n) // s.card = 2}) : Prop := (two_token_kmn_lefts v).card = 2
