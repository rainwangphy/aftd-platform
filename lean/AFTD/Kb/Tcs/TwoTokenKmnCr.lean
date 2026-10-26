import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmnLr
import AFTD.Kb.Tcs.TwoTokenKmnRights
import AFTD.Kb.Tcs.TwoTokenKmnLefts

/-!
# two_token_kmn_cr

Topic: graphs   Node: dcb515e1e8ac

Provenance: helper lemma. step towards two_token_kmn_domination_number

The set of right vertices appearing in an LR vertex of S (the 'C-right' set, of size beta).
-/

/-- Right vertices used by the LR part of S; its cardinality is beta. -/
abbrev two_token_kmn_cr {m n : ℕ} (S : Finset {s : Finset (Fin m ⊕ Fin n) // s.card = 2}) : Finset (Fin n) := (S.filter two_token_kmn_lr).biUnion two_token_kmn_rights
