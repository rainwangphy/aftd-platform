import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmnLr
import AFTD.Kb.Tcs.TwoTokenKmnLefts

/-!
# two_token_kmn_cl

Topic: graphs   Node: 9004b7524f95

Provenance: helper lemma. step towards two_token_kmn_domination_number

The set of left vertices appearing in an LR vertex of S (the 'C-left' set, of size alpha).
-/

/-- Left vertices used by the LR part of S; its cardinality is alpha. -/
abbrev two_token_kmn_cl {m n : ℕ} (S : Finset {s : Finset (Fin m ⊕ Fin n) // s.card = 2}) : Finset (Fin m) := (S.filter two_token_kmn_lr).biUnion two_token_kmn_lefts
