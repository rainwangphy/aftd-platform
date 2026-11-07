import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSixCirculant

/-!
# digraph_six_circulant_decidable

Topic: graphs   Node: a1cfd785c1bb

Provenance: helper lemma. step towards digraph_ckk_subdivision_three_exceptional

The adjacency relation of `digraph_six_circulant` is decidable.
-/

/-- Decidability of the adjacency of `digraph_six_circulant`, needed to settle its finite properties by `decide`. -/
instance digraph_six_circulant_decidable : DecidableRel digraph_six_circulant.Adj := fun a b => by unfold digraph_six_circulant; infer_instance
