import AFTD.Prelude

/-!
# finite_cubic_ten_connector_count_and_forced_edge

Topic: graphs   Node: 3a2534ac103b

Provenance: helper lemma. Finite connector count underlying the 120-vertex packing-choice obstruction; experiments 17176 and 17181.

For the specified fifteen-edge cubic graph and the designated root edge 01, any vertex subset S contains at most four more vertices than selected non-root edges; if equality holds and S does not contain both root endpoints then there is a non-root edge whose endpoints both lie outside S.
-/

theorem finite_cubic_ten_connector_count_and_forced_edge :
    let E : Finset (Fin 10 × Fin 10) :=
      {(0,1),(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),
       (3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9)}
    let D := E.erase (0,1)
    ∀ S : Finset (Fin 10),
      let inside := D.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)
      S.card ≤ 4 + inside.card ∧
      (S.card = 4 + inside.card → (0 ∉ S ∨ 1 ∉ S) →
        ∃ e ∈ D, e.1 ∉ S ∧ e.2 ∉ S) := by
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 0 in
      decide
