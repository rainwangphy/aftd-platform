import AFTD.Prelude

/-!
# op_193_disjoint_anchor_packings

Topic: graphs   Node: 6b22372e4bc4

Provenance: helper lemma. Finite obstructions to overlap-only improvements of the anchor edge count; experiment 23383.

The thirteen-cycle has nine stable triples and the fourteen-cycle has ten stable triples, respectively, with any two triples sharing at most one vertex.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def in777_pack13 : Fin 9 → Finset (Fin 13) := ![{0,3,6}, {0,8,10}, {0,9,11}, {1,6,9}, {1,7,11}, {2,4,8}, {2,6,12}, {2,7,10}, {5,9,12}]

private def in777_pack14 : Fin 10 → Finset (Fin 14) := ![{0,3,7}, {0,8,10}, {1,3,5}, {1,10,13}, {2,4,12}, {2,5,8}, {2,6,11}, {2,9,13}, {3,6,10}, {6,8,13}]

theorem op_193_disjoint_anchor_packings :
    (∃ A : Fin 9 → Finset (Fin 13),
      (∀ j, (A j).card = 3 ∧ (SimpleGraph.cycleGraph 13).IsIndepSet (↑(A j) : Set (Fin 13))) ∧
      ∀ i j, i ≠ j → ((A i) ∩ (A j)).card ≤ 1) ∧
    (∃ A : Fin 10 → Finset (Fin 14),
      (∀ j, (A j).card = 3 ∧ (SimpleGraph.cycleGraph 14).IsIndepSet (↑(A j) : Set (Fin 14))) ∧
      ∀ i j, i ≠ j → ((A i) ∩ (A j)).card ≤ 1) := by
  exact ⟨⟨in777_pack13, by decide⟩, ⟨in777_pack14, by decide⟩⟩
