import AFTD.Prelude
import AFTD.Kb.Tcs.GraphConfigStackable
import AFTD.Kb.Tcs.GraphPebblingStep

/-!
# graph_config_stackable_single

Topic: graphs   Node: acec1c24cc1e

Provenance: helper lemma. Sanity lemma for graph_config_stackable (arXiv:2610.09650 (The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem), Definition 2.1).

A configuration with m ≥ 1 pebbles all on one vertex is stackable (it is already stacked).
-/

theorem graph_config_stackable_single {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v : V)
    (m : ℕ) (hm : 0 < m) : graph_config_stackable G (Pi.single v m) :=
  ⟨_, Relation.ReflTransGen.refl, v, by simpa using hm, fun w hw => by simp [hw]⟩
