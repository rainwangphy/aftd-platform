import AFTD.Prelude

/-!
# connected_graph_delete_false_twin_connected

Topic: graphs   Node: 0a8283b2cda5

Provenance: helper lemma. Elementary connectivity for the OP-1957 unrestricted twin-bridge route.

Deleting one of two distinct false twins from a connected graph leaves it connected.
-/

theorem connected_graph_delete_false_twin_connected {V : Type*} (G : SimpleGraph V) (hconn : G.Connected) (x y : V) (hxy : x ≠ y) (htwin : G.neighborSet x = G.neighborSet y) : (G.induce {a | a ≠ y}).Connected := by
  classical
  let f : V → {a : V // a ≠ y} := fun a =>
    ⟨if a = y then x else a, by split_ifs with h <;> assumption⟩
  have hadj : ∀ a b, G.Adj a b → (G.induce {a | a ≠ y}).Adj (f a) (f b) := by
    intro a b hab
    by_cases ha : a = y
    · subst a
      have hb : b ≠ y := by intro h; subst b; exact G.irrefl hab
      have hxb : G.Adj x b := by
        change b ∈ G.neighborSet x
        rw [htwin]
        exact hab
      simpa [f, hb] using hxb
    · by_cases hb : b = y
      · subst b
        have hxa : G.Adj x a := by
          change a ∈ G.neighborSet x
          rw [htwin]
          exact hab.symm
        simpa [f, ha] using hxa.symm
      · simpa [f, ha, hb] using hab
  let F : G →g (G.induce {a | a ≠ y}) := ⟨f, fun {a b} h => hadj a b h⟩
  apply SimpleGraph.Connected.map F ?_ hconn
  intro a
  refine ⟨a.val, ?_⟩
  apply Subtype.ext
  have ha : a.val ≠ y := a.property
  simp [F, f, ha]
