import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmn

/-!
# two_token_kmn_rights

Topic: graphs   Node: 653c3fc6fd45

Provenance: helper lemma. step towards two_token_kmn_domination_number

The set of right vertices (in Fin n) occurring in a 2-element vertex {u,v} of F_2(K_{m,n}).
-/

/-- Right part of a 2-token vertex of F_2(K_{m,n}). -/
abbrev two_token_kmn_rights {m n : ℕ} (v : {s : Finset (Fin m ⊕ Fin n) // s.card = 2}) : Finset (Fin n) := v.val.biUnion (fun a => match a with | Sum.inl _ => ∅ | Sum.inr y => {y})
