import AFTD.Prelude
import AFTD.Kb.Tcs.DiamondMove
import AFTD.Kb.Tcs.MaximalChainLowerSet

/-!
# mcdo_le

Topic: combinatorics   Node: 81cd27866664

Provenance: formalization of a published result. Source: arXiv:2611.26888 Definition 2.2

The maximal chain descent order relation mcdo_le l on maximal chains of order ideals M M' of type MaximalChainLowerSet P of a finite partially ordered set P under a labeling l : P → Fin (Fintype.card P) is the reflexive and transitive closure Relation.ReflTransGen of diamond_move l.
-/

/-- The maximal chain descent order (MCDO) on maximal chains of order ideals induced by a linear extension. -/
def mcdo_le {P : Type*} [PartialOrder P] [Fintype P]
    (l : P → Fin (Fintype.card P)) (M M' : MaximalChainLowerSet P) : Prop := Relation.ReflTransGen (diamond_move l) M M'
