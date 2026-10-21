import AFTD.Prelude
import AFTD.Kb.Tcs.CubicPaleyGraph

/-!
# cubic_paley_graph_decidable_adj

Topic: graphs   Node: 1fcf3a302ebf

Provenance: helper lemma. decidability for cubic_paley_graph; serves OP-442

Adjacency in the cubic Paley graph over a finite ring with decidable equality is decidable.
-/

instance cubic_paley_graph_decidable_adj (F : Type*) [CommRing F] [Fintype F] [DecidableEq F] :
    DecidableRel (cubic_paley_graph F).Adj :=
  fun x y => decidable_of_iff (x ≠ y ∧ ∃ z : F, x - y = z ^ 3) Iff.rfl
