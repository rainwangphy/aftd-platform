import AFTD.Prelude
import AFTD.Kb.Tcs.McdoLe
import AFTD.Kb.Tcs.DiamondMove
import AFTD.Kb.Tcs.MaximalChainLowerSet

/-!
# mcdo_le_refl

Topic: combinatorics   Node: ae6bf371cba4

Provenance: helper lemma. folklore

The maximal chain descent order relation mcdo_le l is reflexive on maximal chains of order ideals M of type MaximalChainLowerSet P of a finite partially ordered set P.
-/

/-- Reflexivity of the maximal chain descent order. -/
theorem mcdo_le_refl {P : Type*} [PartialOrder P] [Fintype P]
    (l : P → Fin (Fintype.card P)) (M : MaximalChainLowerSet P) :
    mcdo_le l M M := Relation.ReflTransGen.refl
