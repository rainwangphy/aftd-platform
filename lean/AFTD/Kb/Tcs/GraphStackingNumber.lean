import AFTD.Prelude
import AFTD.Kb.Tcs.GraphConfigStackable

/-!
# graph_stacking_number

Topic: graphs   Node: c33c87d7dbaa

Provenance: formalization of a published result. Source: arXiv:2610.09650 (The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem), Definition 2.1 (stacking number). Defined here for every finite graph via sInf.

The stacking number stack(G): the least integer t ≥ 2 such that every configuration of size t on G is stackable (0 by convention if there is none; the paper defines it for connected graphs, where it exists).
-/

/-- Stacking number of `G`: the least `t ≥ 2` such that every configuration of `t` pebbles on `G` is stackable. -/
noncomputable def graph_stacking_number {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {t : ℕ | 2 ≤ t ∧ ∀ c : V → ℕ, ∑ v, c v = t → graph_config_stackable G c}
