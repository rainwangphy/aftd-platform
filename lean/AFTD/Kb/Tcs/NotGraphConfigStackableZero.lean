import AFTD.Prelude
import AFTD.Kb.Tcs.GraphConfigStackable
import AFTD.Kb.Tcs.GraphPebblingStep

/-!
# not_graph_config_stackable_zero

Topic: graphs   Node: a38cdb070228

Provenance: helper lemma. Sanity lemma for graph_config_stackable (arXiv:2610.09650 (The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem), Definition 2.1).

The empty configuration is not stackable: no step applies and its support is empty.
-/

theorem not_graph_config_stackable_zero {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    ¬ graph_config_stackable G 0 := by
  rintro ⟨c', hr, v, hv, -⟩
  have : c' = 0 := by
    clear hv
    induction hr with
    | refl => rfl
    | tail _ hstep ih =>
      subst ih
      obtain ⟨u, w, -, hu, -⟩ := hstep
      simp at hu
  subst this
  simp at hv
