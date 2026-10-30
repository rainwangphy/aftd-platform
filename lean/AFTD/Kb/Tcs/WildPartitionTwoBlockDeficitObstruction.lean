import AFTD.Prelude
import AFTD.Kb.Tcs.WildPartitionSingleSwapObstruction
import AFTD.Kb.Tcs.WildPartitionSingleSwapDeficitObstruction
import AFTD.Kb.Tcs.WildJointFirstBlockMixedReduction
import AFTD.Kb.Tcs.WildJointBadRelation

/-!
# wild_partition_two_block_deficit_obstruction

Topic: graphs   Node: ed875210c628

Provenance: helper lemma. IN-385 / OP-306 campaign10,2026-10-30. Internal structural-route diagnostic for https://arxiv.org/html/2610.22142v1 Sections3.3/6. Targeted SAT experiment9745 and independent NetworkX audit9751 found and checked this explicit array; the proof uses kernel-checked finite cut/path certificates and ordinary connected-component cardinal arguments. This is not a published-paper erratum, a main conjecture refutation, a new wild-number case, or a research advance.

For the same explicit15 array, every way of choosing two distinct original triple blocks and a three-element subset of their six local positions, then replacing those blocks by that subset and its complement, preserves all block sizes3 and has component deficit at least1. The starting deficit is1, and the displayed three-block repair has deficit0. This exhausts the two-block repartition neighborhood and refutes strict two-block deficit descent, not plateau search or the main wild-number conjecture.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

def in385_two_block_code (U : Finset (Fin 6)) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 4, 1, 0, 0, 0, 0, 8, 0, 5, 2, 0, 0, 12, 15, 0, 18, 0, 0, 0, 0, 0, 0, 9, 0, 6, 3, 0, 0, 11, 14, 0, 17, 0, 0, 0, 0, 10, 13, 0, 16, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (∑ j∈U,2^j.val) 0

def in385_two_block_left (b : Fin 5) (U : Finset (Fin 6)) : Fin 15 :=
  ⟨3*b.val+(in385_two_block_code U-1)%9/3,by
    have := b.isLt
    have := Nat.mod_lt (in385_two_block_code U-1) (by omega : 0<9)
    omega⟩

def in385_two_block_right (b d : Fin 5) (U : Finset (Fin 6)) : Fin 15 :=
  if in385_two_block_code U=0 ∨ in385_two_block_code U=19 then in385_two_block_left b U
  else ⟨3*d.val+(in385_two_block_code U-1)%3,by
    have := d.isLt
    have := Nat.mod_lt (in385_two_block_code U-1) (by omega : 0<3)
    omega⟩

def in385_two_block_label_swap (b d : Fin 5) (U : Finset (Fin 6)) :
    Equiv.Perm (Fin 5) :=
  if 10 ≤ in385_two_block_code U then Equiv.swap b d else Equiv.refl _

def in385_two_block_slot (b : Fin 5) (v : Fin 15) : Fin 6 :=
  ⟨v.val%3+(if in385_trap_block v=b then 0 else 3),by
    have := Nat.mod_lt v.val (by omega : 0<3)
    split_ifs <;> omega⟩

def in385_two_block_repartition (b d : Fin 5) (U : Finset (Fin 6)) (v : Fin 15) : Fin 5 :=
  if in385_trap_block v=b ∨ in385_trap_block v=d then
    if in385_two_block_slot b v∈U then b else d
  else in385_trap_block v

theorem in385_two_block_representation : ∀ (b d : Fin 5) (U : Finset (Fin 6)),
    b≠d → U.card=3 → ∀ v : Fin 15,
      in385_two_block_repartition b d U v =
        in385_two_block_label_swap b d U
          (in385_trap_swap_block (in385_two_block_left b U) (in385_two_block_right b d U) v) := by
  decide +kernel

theorem in385_two_block_card : ∀ (b d : Fin 5) (U : Finset (Fin 6)),
    b≠d → U.card=3 → ∀ j : Fin 5,
      (univ.filter fun v => in385_two_block_repartition b d U v=j).card=3 := by
  decide +kernel

theorem wild_partition_two_block_deficit_obstruction :
    in385_trap_deficit in385_trap_block=1 ∧
    (∀ (b d : Fin 5) (U : Finset (Fin 6)),b≠d → U.card=3 →
      (∀ j : Fin 5,(univ.filter fun v => in385_two_block_repartition b d U v=j).card=3) ∧
      1 ≤ in385_trap_deficit (in385_two_block_repartition b d U)) ∧
    in385_trap_deficit in385_trap_repair_block=0 := by
  refine ⟨in385_trap_base_deficit,?_,wild_partition_single_swap_deficit_obstruction.2.2⟩
  intro b d U hbd hU
  refine ⟨in385_two_block_card b d U hbd hU,?_⟩
  obtain ⟨i,hi⟩ := wild_partition_single_swap_obstruction.2.2.2.2.2
    (in385_two_block_left b U) (in385_two_block_right b d U)
  apply in385_trap_deficit_pos_of_bad (in385_two_block_repartition b d U) i
  have hp : in385_two_block_repartition b d U =
      fun v => in385_two_block_label_swap b d U
        (in385_trap_swap_block (in385_two_block_left b U) (in385_two_block_right b d U) v) :=
    funext (in385_two_block_representation b d U hbd hU)
  rw [hp]
  exact (wild_joint_bad_relation_block_relabel 5
    (in385_trap_swap_block (in385_two_block_left b U) (in385_two_block_right b d U))
    (fun x y => x≠y ∧ in385_trap_array x y=i)
    (in385_two_block_label_swap b d U)).mpr hi
