import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleTwoOddAnticompleteShoresComplementUnmatchable
import AFTD.Kb.Tcs.PerfectMatchingOfAdjacencyInvolution

/-!
# boundary_seven_block_example_cross_edge_essential

Topic: graphs   Node: 2dc2acec6151

Provenance: helper lemma. OP-1957: explicit odd-shore obstruction; experiments 37010 and 37011.

In the explicitly defined 28-vertex four-block graph, the edge from 0 to 14 is present, and deleting it leaves a graph that is not 7-extendible.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def in1122_block28 (v : Fin 28) : ℕ :=
  if v.val < 5 then 0 else if v.val < 14 then 1 else if v.val < 19 then 2 else 3

def in1122_edge28 (u v : Fin 28) : Prop :=
  u ≠ v ∧
  (in1122_block28 u = in1122_block28 v ∨ ((u.val < 14) ≠ (v.val < 14))) ∧
  (min u.val v.val, max u.val v.val) ∉
    ([(0,21),(3,14),(3,21),(4,14),(4,21)] : List (ℕ × ℕ))

instance : DecidableRel in1122_edge28 := fun _ _ => by
  unfold in1122_edge28 in1122_block28
  infer_instance

def in1122_boundary_graph28 : SimpleGraph (Fin 28) where
  Adj := in1122_edge28
  symm := by
    constructor
    intro u v h
    rcases h with ⟨hne, hs, he⟩
    refine ⟨hne.symm, ?_, ?_⟩
    · rcases hs with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Ne.symm h)
    · simpa [min_comm, max_comm] using he
  loopless := by constructor; intro u h; exact h.1 rfl

instance : DecidableRel in1122_boundary_graph28.Adj :=
  inferInstanceAs (DecidableRel in1122_edge28)

def in1122_left28 : Finset (Fin 28) := {0,3,4}
def in1122_right28 : Finset (Fin 28) := {5,6,7,8,9,10,11,12,13,14,21}

def in1122_mate28 : Fin 28 → Fin 28 :=
  ![0,2,1,3,4,5,6,7,8,9,10,11,12,13,14,16,15,18,17,20,19,21,23,22,25,24,27,26]

theorem boundary_seven_block_example_cross_edge_essential :
    in1122_boundary_graph28.Adj 0 14 ∧
    ¬ is_k_extendable (in1122_boundary_graph28.deleteEdges {s(0,14)}) 7 := by
  classical
  constructor
  · decide
  · intro hExt
    let Z := in1122_boundary_graph28.deleteEdges {s(0,14)}
    let C : Finset (Fin 28) := Finset.univ.filter
      (fun v => v ∉ in1122_left28 ∧ v ∉ in1122_right28)
    let fC (v : {v : Fin 28 // v ∈ C}) : {v : Fin 28 // v ∈ C} :=
      ⟨in1122_mate28 v.val, by revert v; decide⟩
    have fC_inv (v : {v : Fin 28 // v ∈ C}) : fC (fC v) = v := by
      revert v; decide
    have fC_adj (v : {v : Fin 28 // v ∈ C}) :
        (Z.induce {x | x ∈ C}).Adj v (fC v) := by
      revert v; decide
    have hT : in1122_left28.card % 2 = 1 := by decide
    have hN : in1122_right28.card % 2 = 1 := by decide
    have hdisj : Disjoint in1122_left28 in1122_right28 := by decide
    have hcross : ∀ a ∈ in1122_left28, ∀ b ∈ in1122_right28, ¬ Z.Adj a b := by
      decide
    have hsize : ({v : Fin 28 | v ∉ in1122_left28 ∧ v ∉ in1122_right28} : Set (Fin 28)).ncard = 2*7 := by
      have heq : ({v : Fin 28 | v ∉ in1122_left28 ∧ v ∉ in1122_right28} : Set (Fin 28)) = (C : Set (Fin 28)) := by
        ext x
        simp [C]
      rw [heq, Set.ncard_coe_finset]
      decide
    have hPM : ∃ P : (Z.induce {v | v ∉ in1122_left28 ∧ v ∉ in1122_right28}).Subgraph, P.IsPerfectMatching := by
      have heq : {v : Fin 28 | v ∉ in1122_left28 ∧ v ∉ in1122_right28} = {v | v ∈ C} := by
        ext x
        simp [C]
      rw [heq]
      exact perfect_matching_of_adjacency_involution _ fC fC_inv fC_adj
    exact extendible_two_odd_anticomplete_shores_complement_unmatchable Z 7
      hExt in1122_left28 in1122_right28 hT hN hdisj hcross hsize hPM
