import AFTD.Prelude
import AFTD.Kb.Tcs.Op874ShortestDirectedWalkIsPath

/-!
# op874_exists_shortest_directed_path

Topic: graphs   Node: d37796c82743

Provenance: helper lemma. Choose a minimal length walk; bypass preserves directed darts.

If a directed walk obeying a dart predicate exists, a shortest one exists and is simple.
-/

theorem op874_exists_shortest_directed_path {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (P : G.Dart → Prop) {u v : V}
    (h : ∃ w : G.Walk u v, ∀ e ∈ w.darts, P e) :
    ∃ w : G.Walk u v, w.IsPath ∧ (∀ e ∈ w.darts, P e) ∧
      ∀ w' : G.Walk u v, (∀ e ∈ w'.darts, P e) → w.length ≤ w'.length := by
  classical
  have hn : ∃ n : ℕ, ∃ w : G.Walk u v, w.length = n ∧ ∀ e ∈ w.darts, P e := by
    obtain ⟨w, hw⟩ := h
    exact ⟨w.length, w, rfl, hw⟩
  obtain ⟨w, hwlen, hw⟩ := Nat.find_spec hn
  have hmin (w' : G.Walk u v) (hw' : ∀ e ∈ w'.darts, P e) : w.length ≤ w'.length := by
    rw [hwlen]
    exact Nat.find_min' hn ⟨w', rfl, hw'⟩
  exact ⟨w, op874_shortest_directed_walk_is_path G P w hw hmin, hw, hmin⟩
