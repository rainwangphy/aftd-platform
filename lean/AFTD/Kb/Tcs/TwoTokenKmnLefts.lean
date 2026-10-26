import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmn

/-!
# two_token_kmn_lefts

Topic: graphs   Node: 1d946340d700

Provenance: helper lemma. step towards two_token_kmn_domination_number

The set of left vertices (in Fin m) occurring in a 2-element vertex {u,v} of F_2(K_{m,n}).
-/

/-- Left part of a 2-token vertex of F_2(K_{m,n}). -/
abbrev two_token_kmn_lefts {m n : ℕ} (v : {s : Finset (Fin m ⊕ Fin n) // s.card = 2}) : Finset (Fin m) := v.val.biUnion (fun a => match a with | Sum.inl x => {x} | Sum.inr _ => ∅)
