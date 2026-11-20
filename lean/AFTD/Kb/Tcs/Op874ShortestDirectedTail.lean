import AFTD.Prelude

/-!
# op874_shortest_directed_tail

Topic: graphs   Node: 76e0d9d5b4cb

Provenance: helper lemma. A tail of a shortest directed walk is shortest.

The tail of a shortest walk whose darts satisfy a predicate is shortest under the same predicate.
-/

theorem op874_shortest_directed_tail {V : Type*} (G : SimpleGraph V) (P : G.Dart → Prop)
    {u v t : V} (huv : G.Adj u v) (w : G.Walk v t)
    (hfirst : P ⟨(u,v), huv⟩)
    (hmin : ∀ w' : G.Walk u t, (∀ e ∈ w'.darts, P e) → (SimpleGraph.Walk.cons huv w).length ≤ w'.length) :
    ∀ w' : G.Walk v t, (∀ e ∈ w'.darts, P e) → w.length ≤ w'.length := by
  intro w' hw'
  have hh : ∀ e ∈ (SimpleGraph.Walk.cons huv w').darts, P e := by
    intro e he
    simp only [SimpleGraph.Walk.darts_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact hfirst
    · exact hw' e he
  have h := hmin (SimpleGraph.Walk.cons huv w') hh
  simp only [SimpleGraph.Walk.length_cons] at h
  omega
