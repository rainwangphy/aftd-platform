import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmn

/-!
# two_token_kmn_ll_vertex

Topic: graphs   Node: e039b215786f

Provenance: helper lemma. step towards two_token_kmn_domination_number

The LL vertex {x,y} determined by two distinct left vertices x != y.
-/

/-- Canonical LL vertex of F_2(K_{m,n}). -/
abbrev two_token_kmn_ll_vertex {m n : ℕ} (x y : Fin m) (h : x ≠ y) : {s : Finset (Fin m ⊕ Fin n) // s.card = 2} := ⟨{Sum.inl x, Sum.inl y}, by simp [h]⟩
