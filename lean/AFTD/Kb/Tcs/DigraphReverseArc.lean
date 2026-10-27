import AFTD.Prelude

/-!
# digraph_reverse_arc

Topic: graphs   Node: 2269ef83b6ae

Provenance: helper lemma. step towards tournament_not_near_regular_exists_improving_tournament

The digraph obtained from D by reversing the arc between u and v: the two vertices exchange which of them points to the other, and every other adjacency is untouched.
-/

/-- Reverse the single arc between u and v of a digraph. -/
abbrev digraph_reverse_arc {n : ℕ} (D : Digraph (Fin n)) (u v : Fin n) : Digraph (Fin n) := ⟨fun x y => if (x = u ∧ y = v) ∨ (x = v ∧ y = u) then D.Adj y x else D.Adj x y⟩
