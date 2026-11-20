import AFTD.Prelude

/-!
# op309_leaf_extension_fixed_table_obstruction

Topic: graphs   Node: 5de8cadece21

Provenance: helper lemma. OP-309 pendant-leaf boundary test; experiment 36525.

The explicit six-edge adjacency/color table is a proper rich-neighbor coloring with two designated rich boundary edges, but none of the five colors for an added seventh edge gives a proper rich-neighbor coloring of the displayed extended table.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option maxSynthPendingDepth 64

namespace In1099LeafKernel

def edges : Fin 7 → (Fin 6 × Fin 6) := ![(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(4,5)]

def adj (i j : Fin 7) : Prop :=
  i ≠ j ∧ ((edges i).1 = (edges j).1 ∨ (edges i).1 = (edges j).2 ∨
    (edges i).2 = (edges j).1 ∨ (edges i).2 = (edges j).2)
instance (i j : Fin 7) : Decidable (adj i j) := by unfold adj; infer_instance

def baseAdj (i j : Fin 6) : Prop := adj ⟨i.val,by omega⟩ ⟨j.val,by omega⟩
instance (i j : Fin 6) : Decidable (baseAdj i j) := by unfold baseAdj; infer_instance

def baseColor : Fin 6 → Fin 5 := ![0,1,2,1,3,4]
def extColor (x : Fin 5) : Fin 7 → Fin 5 := ![0,1,2,1,3,4,x]

def proper {n : Nat} (A : Fin n → Fin n → Prop) (c : Fin n → Fin 5) : Prop :=
  ∀ i j, A i j → c i ≠ c j

def rich {n : Nat} (A : Fin n → Fin n → Prop) (c : Fin n → Fin 5) (i : Fin n) : Prop :=
  ∀ j k, A i j → A i k → j ≠ k → c j ≠ c k

def richNeighbor {n : Nat} (A : Fin n → Fin n → Prop) (c : Fin n → Fin 5) : Prop :=
  ∀ i, (∃ j, A i j) → ∃ j, A i j ∧ rich A c j

theorem base_works : proper baseAdj baseColor ∧ richNeighbor baseAdj baseColor ∧
    rich baseAdj baseColor 2 ∧ rich baseAdj baseColor 5 := by
  refine ⟨?_,?_,?_,?_⟩
  · unfold proper; decide
  · unfold richNeighbor rich; decide
  · unfold rich; decide
  · unfold rich; decide

theorem no_fixed_extension (x : Fin 5) :
    ¬ (proper adj (extColor x) ∧ richNeighbor adj (extColor x)) := by
  intro ⟨hp,hr⟩
  fin_cases x
  all_goals first
    | (clear hp; revert hr; unfold richNeighbor rich; decide)
    | (clear hr; revert hp; unfold proper; decide)

end In1099LeafKernel

theorem op309_leaf_extension_fixed_table_obstruction : In1099LeafKernel.proper In1099LeafKernel.baseAdj In1099LeafKernel.baseColor ∧ In1099LeafKernel.richNeighbor In1099LeafKernel.baseAdj In1099LeafKernel.baseColor ∧ In1099LeafKernel.rich In1099LeafKernel.baseAdj In1099LeafKernel.baseColor 2 ∧ In1099LeafKernel.rich In1099LeafKernel.baseAdj In1099LeafKernel.baseColor 5 ∧ ∀ x : Fin 5, ¬ (In1099LeafKernel.proper In1099LeafKernel.adj (In1099LeafKernel.extColor x) ∧ In1099LeafKernel.richNeighbor In1099LeafKernel.adj (In1099LeafKernel.extColor x)) := by exact ⟨In1099LeafKernel.base_works.1, In1099LeafKernel.base_works.2.1, In1099LeafKernel.base_works.2.2.1, In1099LeafKernel.base_works.2.2.2, In1099LeafKernel.no_fixed_extension⟩
