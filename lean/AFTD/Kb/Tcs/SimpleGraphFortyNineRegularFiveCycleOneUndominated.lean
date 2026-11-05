import AFTD.Prelude

/-!
# simple_graph_forty_nine_regular_five_cycle_one_undominated

Topic: combinatorics   Node: 4657d64446b2

Provenance: original. Related work: OP-926, experiments 14647 and 15034; this graph has independent ten-sets and does not refute the Ramsey statement.

There is a triangle-free 9-regular simple graph on 40 vertices and a five-vertex set whose induced graph has degree two at every vertex, such that exactly one vertex has no neighbor in that set.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace In555

def masks : Fin 40 → Nat := ![8114, 1040389, 66060330, 8522825748, 1090921693193, 144821452805, 769336018304, 235348033, 2249654337, 534725591041, 36541194305, 68888240129, 191932137473, 567478848642, 231951303682, 156703391746, 9139391362, 154904038786, 274888400258, 1162876962, 953483264260, 5771649540, 281321005060, 728265719812, 831613714436, 288299683204, 661425521032, 858995591336, 77320065064, 50442344, 936305524744, 29366056, 17244881000, 1443971152, 4296208912, 1284511248, 1410353744, 8573552, 1263796752, 1301291088]
def rel (u v : Fin 40) : Prop := (masks u).testBit v.val = true
instance (u v : Fin 40) : Decidable (rel u v) := inferInstanceAs (Decidable ((masks u).testBit v.val = true))
theorem rel_symm : ∀ u v, rel u v → rel v u := by decide
theorem rel_irrefl : ∀ u, ¬ rel u u := by decide
def graph : SimpleGraph (Fin 40) where
  Adj := rel
  symm := ⟨rel_symm⟩
  loopless := ⟨rel_irrefl⟩
instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (rel _ _))

def cycle : Finset (Fin 40) := {0, 1, 2, 3, 4}
theorem certificate :
    (∀ v, graph.degree v = 9) ∧
    (∀ a b c, graph.Adj a b → graph.Adj b c → ¬ graph.Adj a c) ∧
    cycle.card = 5 ∧
    (∀ v ∈ cycle, ((graph.neighborFinset v) ∩ cycle).card = 2) ∧
    (∀ x, (∀ t ∈ cycle, ¬ graph.Adj t x) ↔ x = 6) := by
  refine ⟨?_, ?_, by decide, ?_, ?_⟩
  · intro v; fin_cases v <;> decide
  · intro a; fin_cases a <;> decide
  · decide
  · decide
end In555

theorem simple_graph_forty_nine_regular_five_cycle_one_undominated :
    ∃ (G : SimpleGraph (Fin 40)) (d : DecidableRel G.Adj) (T : Finset (Fin 40)),
      letI := d
      (∀ v, G.degree v = 9) ∧
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c) ∧
      T.card = 5 ∧
      (∀ v ∈ T, ((G.neighborFinset v) ∩ T).card = 2) ∧
      (∃ x, ∀ y, (∀ t ∈ T, ¬ G.Adj t y) ↔ y = x) := by
  refine ⟨In555.graph, inferInstance, In555.cycle, ?_⟩
  obtain ⟨hreg, htri, hcard, hcycle, hmiss⟩ := In555.certificate
  exact ⟨hreg, htri, hcard, hcycle, ⟨6, hmiss⟩⟩
