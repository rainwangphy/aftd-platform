import AFTD.Prelude

/-!
# op309_vertexwise_four_tables_core

Topic: graphs   Node: 8a1ce5d0b046

Provenance: helper lemma. OP-309 vertexwise fixed-forest obstruction; experiments 40589 and 40590.

Each of the four valid port tables has five core classes with three triple hosts per class, and every class pair shares a host.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace Op309VertexwiseCore

def hosts : Fin 4 → List (Finset (Fin 8)) := ![
  [{0,1,6},{1,2,7},{1,2,3},{1,2,4},{2,4,5},{0,2,4},{1,4,7},{0,1,2},{3,5,6},{0,1,7}],
  [{0,1,6},{1,2,7},{1,2,3},{1,2,4},{0,2,5},{0,2,4},{0,1,7},{0,1,2},{3,5,6},{1,4,7}],
  [{0,1,6},{1,2,7},{0,2,3},{1,2,4},{1,2,5},{0,1,4},{0,2,7},{0,1,2},{3,5,6},{1,4,7}],
  [{0,1,7},{1,2,3},{2,3,4},{1,2,5},{1,2,6},{1,3,5},{0,2,3},{0,1,2},{4,6,7},{0,1,5}]]

def cores : Fin 4 → Finset (Fin 8) := ![
  {0,1,2,4,7}, {0,1,2,4,7}, {0,1,2,4,7}, {0,1,2,3,5}]

def validCore (i : Fin 4) : Bool :=
  decide ((cores i).card = 5) &&
  ((List.finRange 8).all fun a => decide (a ∉ cores i) ||
    decide (3 ≤ ((hosts i).filter fun H =>
      a ∈ H ∧ 3 ≤ (H ∩ cores i).card).length)) &&
  ((List.finRange 8).all fun a => (List.finRange 8).all fun b =>
    decide (a ∉ cores i) || decide (b ∉ cores i) || decide (a = b) ||
      (hosts i).any fun H => decide (a ∈ H ∧ b ∈ H))

end Op309VertexwiseCore

theorem op309_vertexwise_four_tables_core : ∀ i : Fin 4, Op309VertexwiseCore.validCore i = true := by intro i; fin_cases i <;> decide
