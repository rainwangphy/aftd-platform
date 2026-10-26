import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmnLl
import AFTD.Kb.Tcs.TwoTokenKmnLefts

/-!
# two_token_kmn_al

Topic: graphs   Node: 23f2adc716f1

Provenance: helper lemma. step towards two_token_kmn_domination_number

The set of left vertices covered by the LL vertices of S (the 'A-part' of S).
-/

/-- Left vertices appearing in an LL vertex of S; so m - #(al S) = the parameter u. -/
abbrev two_token_kmn_al {m n : ℕ} (S : Finset {s : Finset (Fin m ⊕ Fin n) // s.card = 2}) : Finset (Fin m) := (S.filter two_token_kmn_ll).biUnion two_token_kmn_lefts
