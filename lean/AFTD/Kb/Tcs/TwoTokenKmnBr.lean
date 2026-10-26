import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmnRr
import AFTD.Kb.Tcs.TwoTokenKmnRights
import AFTD.Kb.Tcs.TwoTokenKmnLefts

/-!
# two_token_kmn_br

Topic: graphs   Node: f65f039cd7ae

Provenance: helper lemma. step towards two_token_kmn_domination_number

The set of right vertices covered by the RR vertices of S (the 'B-part' of S).
-/

/-- Right vertices appearing in an RR vertex of S; so n - #(br S) = the parameter v. -/
abbrev two_token_kmn_br {m n : ℕ} (S : Finset {s : Finset (Fin m ⊕ Fin n) // s.card = 2}) : Finset (Fin n) := (S.filter two_token_kmn_rr).biUnion two_token_kmn_rights
