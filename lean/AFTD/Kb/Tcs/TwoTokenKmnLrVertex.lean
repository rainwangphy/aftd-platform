import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenKmn

/-!
# two_token_kmn_lr_vertex

Topic: graphs   Node: 92e81ba34c7d

Provenance: helper lemma. step towards two_token_kmn_domination_number

The LR vertex {x,y} determined by a left vertex x and a right vertex y.
-/

/-- Canonical LR vertex of F_2(K_{m,n}). -/
abbrev two_token_kmn_lr_vertex {m n : ℕ} (x : Fin m) (y : Fin n) : {s : Finset (Fin m ⊕ Fin n) // s.card = 2} := ⟨{Sum.inl x, Sum.inr y}, by simp⟩
