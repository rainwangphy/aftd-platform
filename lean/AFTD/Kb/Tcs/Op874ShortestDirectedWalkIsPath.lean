import AFTD.Prelude

/-!
# op874_shortest_directed_walk_is_path

Topic: graphs   Node: 28918acf7644

Provenance: helper lemma. Path bypass preserves oriented darts.

A shortest walk subject to a predicate on its oriented darts has no repeated vertices.
-/

theorem op874_shortest_directed_walk_is_path {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (P : G.Dart → Prop) {u v : V} (w : G.Walk u v)
    (hdir : ∀ e ∈ w.darts, P e)
    (hmin : ∀ w' : G.Walk u v, (∀ e ∈ w'.darts, P e) → w.length ≤ w'.length) :
    w.IsPath := by
  have hdir' : ∀ e ∈ w.bypass.darts, P e := by
    intro e he
    exact hdir e (w.darts_bypass_subset_darts he)
  have heq : w.bypass = w := w.bypass_eq_self_of_length_le_length_bypass (hmin w.bypass hdir')
  rw [← heq]
  exact w.bypass_isPath
