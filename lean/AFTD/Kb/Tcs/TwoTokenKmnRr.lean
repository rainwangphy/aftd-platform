import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmnLefts

/-!
# two_token_kmn_rr

Topic: graphs   Node: d7e46be8d682

Provenance: helper lemma. step towards two_token_kmn_domination_number

A vertex of F_2(K_{m,n}) is of type RR when both of its elements are right vertices.
-/

/-- The RR class: 2-subsets contained in the right part. -/
abbrev two_token_kmn_rr {m n : ℕ} (v : {s : Finset (Fin m ⊕ Fin n) // s.card = 2}) : Prop := (two_token_kmn_lefts v).card = 0
