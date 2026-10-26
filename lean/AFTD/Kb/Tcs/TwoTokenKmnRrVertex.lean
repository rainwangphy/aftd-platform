import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmn

/-!
# two_token_kmn_rr_vertex

Topic: graphs   Node: e9d427c8eee7

Provenance: helper lemma. step towards two_token_kmn_domination_number

The RR vertex {x,y} determined by two distinct right vertices x != y.
-/

/-- Canonical RR vertex of F_2(K_{m,n}). -/
abbrev two_token_kmn_rr_vertex {m n : ℕ} (x y : Fin n) (h : x ≠ y) : {s : Finset (Fin m ⊕ Fin n) // s.card = 2} := ⟨{Sum.inr x, Sum.inr y}, by simp [h]⟩
