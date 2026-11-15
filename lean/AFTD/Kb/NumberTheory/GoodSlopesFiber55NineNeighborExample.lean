import AFTD.Prelude

/-!
# good_slopes_fiber55_nine_neighbor_example

Topic: elementary_number_theory   Node: a8f295652bf3

Provenance: helper lemma. Counterexample identified in computation 27575 for the OP-1027 fiber investigation.

There are 55 points over Z/55 containing the two standard anchors with all seven displayed directions good; these directions belong to the nine-neighbor set tested in experiment 27575, disproving the suggested strengthening to at most six of those nine directions.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 15000

theorem good_slopes_fiber55_nine_neighbor_example :
    ∃ S : Finset (ZMod 55 × ZMod 55), S.card = 55 ∧ (0,0) ∈ S ∧ (1,54) ∈ S ∧
      ∀ a ∈ ({23,34,16,21,26,31,36} : Finset (ZMod 55)),
        (S.image fun p => p.2 + a*p.1).card = 55 := by
  let S : Finset (ZMod 55 × ZMod 55) := {
    (0, 0),
    (1, 8),
    (1, 51),
    (1, 54),
    (2, 5),
    (3, 53),
    (4, 23),
    (4, 38),
    (5, 32),
    (6, 17),
    (7, 20),
    (8, 7),
    (9, 27),
    (9, 52),
    (10, 53),
    (11, 31),
    (12, 16),
    (12, 45),
    (13, 25),
    (13, 32),
    (14, 5),
    (15, 46),
    (16, 52),
    (17, 42),
    (18, 15),
    (20, 5),
    (20, 33),
    (20, 45),
    (24, 28),
    (24, 41),
    (25, 41),
    (26, 40),
    (33, 40),
    (34, 50),
    (35, 44),
    (36, 12),
    (37, 21),
    (39, 11),
    (39, 41),
    (40, 17),
    (44, 1),
    (44, 18),
    (44, 37),
    (45, 5),
    (45, 31),
    (45, 46),
    (46, 28),
    (47, 37),
    (49, 0),
    (49, 7),
    (49, 15),
    (49, 27),
    (52, 27),
    (52, 46),
    (52, 52)
  }
  refine ⟨S, by decide, by decide, by decide, ?_⟩
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide
