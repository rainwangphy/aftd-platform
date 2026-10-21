import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverse
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphInvert

/-!
# digraph_dijoin_reverse_eq_inverts

Topic: graphs   Node: 16f8a56a4424

Provenance: helper lemma. step towards tournament_dijoin_inversion_number_symm

The dijoin D̄₁ → D̄₂ equals D₁ → D₂ after inverting the two vertex sets Set.range Sum.inl and Set.range Sum.inr.
-/

/-- The dijoin D̄₁ → D̄₂ is equal to the dijoin D₁ → D₂ with V(D₁) and V(D₂) inverted. -/
theorem digraph_dijoin_reverse_eq_inverts {V W : Type*} (D₁ : Digraph V) (D₂ : Digraph W) :
    digraph_dijoin (digraph_reverse D₁) (digraph_reverse D₂) =
      digraph_invert (digraph_invert (digraph_dijoin D₁ D₂) (Set.range Sum.inl))
        (Set.range Sum.inr) := by
  ext x y
  rcases x with a | a <;> rcases y with b | b <;>
    simp [digraph_dijoin, digraph_reverse, digraph_invert]
