import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointBadRelation

/-!
# wild_partition_single_swap_obstruction

Topic: graphs   Node: fe6a2ce67cfc

Provenance: helper lemma. IN-385 / OP-306 campaign10,2026-10-30. Internal structural-route diagnostic for https://arxiv.org/html/2610.22142v1 Sections3.3/6. Targeted SAT experiment9745 and independent NetworkX audit9751 found and checked this explicit array; the proof uses kernel-checked finite cut/path certificates and ordinary connected-component cardinal arguments. This is not a published-paper erratum, a main conjecture refutation, a new wild-number case, or a research advance.

There is an explicit symmetric idempotent row-injective array on15 vertices, with the consecutive triple partition having no invalid triple, for which every vertex transposition leaves some whole color bad across a nonempty proper block cut. The stored statement includes the exact array normalization, triple sizes, triple validity and all225 transpositions. The component-deficit certificate is a separate supporting theorem; this is not a main conjecture counterexample.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
open Finset
open scoped BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

def in385_trap_array : Fin 15 → Fin 15 → Fin 15 := ![![0,12,14,7,8,1,3,4,2,6,13,5,11,10,9],
  ![12,1,3,14,5,6,4,10,7,0,8,2,13,9,11],
  ![14,3,2,6,13,9,8,12,5,11,4,7,0,1,10],
  ![7,14,6,3,11,10,0,9,1,4,2,13,8,12,5],
  ![8,5,13,11,4,0,14,1,9,2,7,10,6,3,12],
  ![1,6,9,10,0,5,11,13,14,7,12,8,3,4,2],
  ![3,4,8,0,14,11,6,5,10,12,9,1,2,7,13],
  ![4,10,12,9,1,13,5,7,0,8,11,6,14,2,3],
  ![2,7,5,1,9,14,10,0,8,13,3,12,4,11,6],
  ![6,0,11,4,2,7,12,8,13,9,5,3,10,14,1],
  ![13,8,4,2,7,12,9,11,3,5,10,14,1,6,0],
  ![5,2,7,13,10,8,1,6,12,3,14,11,9,0,4],
  ![11,13,0,8,6,3,2,14,4,10,1,9,12,5,7],
  ![10,9,1,12,3,4,7,2,11,14,6,0,5,13,8],
  ![9,11,10,5,12,2,13,3,6,1,0,4,7,8,14]]

def in385_trap_block (v : Fin 15) : Fin 5 := ⟨v.val/3,by have := v.isLt; omega⟩
def in385_trap_swap_block (a b v : Fin 15) : Fin 5 :=
  in385_trap_block (Equiv.swap a b v)
def in385_trap_color : Fin 15 → Fin 15 → Fin 15 := ![![0,0,0,0,5,8,0,3,3,0,0,0,0,0,0],
  ![0,0,0,5,10,2,7,7,2,0,0,0,0,0,0],
  ![0,0,0,7,5,1,9,8,11,0,0,0,0,0,0],
  ![0,5,7,0,0,0,0,0,0,14,3,5,14,4,12],
  ![5,10,5,0,0,0,0,0,0,6,10,8,3,12,5],
  ![8,2,1,0,0,0,0,0,0,4,9,1,9,3,5],
  ![0,7,9,0,0,0,0,0,0,8,3,9,13,1,3],
  ![3,7,8,0,0,0,0,0,0,11,3,10,10,7,6],
  ![3,2,11,0,0,0,0,0,0,12,4,6,8,7,3],
  ![0,0,0,14,6,4,8,11,12,0,0,0,0,0,0],
  ![0,0,0,3,10,9,3,3,4,0,0,0,0,0,0],
  ![0,0,0,5,8,1,9,10,6,0,0,0,0,0,0],
  ![0,0,0,14,3,9,13,10,8,0,0,0,0,0,0],
  ![0,0,0,4,12,3,1,7,7,0,0,0,0,0,0],
  ![0,0,0,12,5,5,3,6,3,0,0,0,0,0,0]]
def in385_trap_mask : Fin 15 → Fin 15 → ℕ := ![![25,25,25,29,5,13,27,19,9,25,25,25,25,25,25],
  ![25,25,25,29,25,21,27,11,1,25,25,25,1,25,25],
  ![25,25,25,21,9,1,25,27,17,1,25,25,25,25,25],
  ![29,29,21,25,25,25,25,25,25,9,23,7,25,29,15],
  ![5,25,9,25,25,25,25,25,25,3,29,13,29,15,29],
  ![13,21,1,25,25,25,25,25,25,29,25,25,17,29,15],
  ![27,27,25,25,25,25,25,25,25,27,9,23,15,7,19],
  ![19,11,27,25,25,25,25,25,25,23,5,25,17,15,27],
  ![9,1,17,25,25,25,25,25,25,5,5,27,15,27,5],
  ![25,25,1,9,3,29,27,23,5,25,25,25,25,25,25],
  ![25,25,25,23,29,25,9,5,5,25,25,25,25,25,25],
  ![25,25,25,7,13,25,23,25,27,25,25,25,25,25,25],
  ![25,1,25,25,29,17,15,17,15,25,25,25,25,25,25],
  ![25,25,25,29,15,29,7,15,27,25,25,25,25,25,25],
  ![25,25,25,15,29,15,19,27,5,25,25,25,25,25,25]]
def in385_trap_cut (a b : Fin 15) : Finset (Fin 5) :=
  univ.filter fun j => (in385_trap_mask a b).testBit j.val = true

def in385_trap_repair_block : Fin 15 → Fin 5 := ![0,0,0,1,1,1,2,2,3,3,3,4,2,4,4]

def in385_trap_mate : Fin 15 → Fin 15 → Fin 15 := ![![0,9,12,6,5,4,3,8,7,1,14,13,2,11,10],
  ![5,1,13,8,7,0,11,4,3,14,12,6,10,2,9],
  ![8,11,2,10,9,14,12,13,0,4,3,1,6,7,5],
  ![6,2,1,3,13,12,0,14,10,11,8,9,5,4,7],
  ![7,6,10,9,4,13,1,0,12,3,2,14,8,5,11],
  ![11,4,8,14,1,5,7,6,2,10,9,0,13,12,3],
  ![9,5,3,2,12,1,6,11,14,0,13,7,4,10,8],
  ![3,8,11,0,10,9,13,7,1,5,4,2,14,6,12],
  ![4,10,6,12,0,11,2,9,8,7,1,5,3,14,13],
  ![14,13,5,7,8,2,10,3,4,9,6,12,11,1,0],
  ![13,7,14,5,11,3,8,1,6,12,10,4,9,0,2],
  ![12,14,9,4,3,6,5,10,13,2,7,11,0,8,1],
  ![1,0,7,13,14,10,9,2,11,6,5,8,12,3,4],
  ![10,12,4,11,2,7,14,5,9,8,0,3,1,13,6],
  ![2,3,0,1,6,8,4,12,5,13,11,10,7,9,14]]

theorem in385_trap_normalized :
    (∀ a,in385_trap_array a a=a) ∧
    (∀ a b,in385_trap_array a b=in385_trap_array b a) ∧
    (∀ a,Function.Injective (in385_trap_array a)) := by
  decide +kernel

theorem in385_trap_blocks_card : ∀ b : Fin 5,
    (univ.filter fun v => in385_trap_block v=b).card=3 := by
  decide +kernel

theorem in385_trap_valid : ∀ i x y : Fin 15,
    x≠y → in385_trap_block x=in385_trap_block i →
    in385_trap_block y=in385_trap_block i → in385_trap_array x y≠i := by
  decide +kernel

theorem in385_trap_mate_color : ∀ i x : Fin 15,
    in385_trap_array x (in385_trap_mate i x)=i := by
  decide +kernel

theorem in385_trap_mate_involution : ∀ i x : Fin 15,
    in385_trap_mate i (in385_trap_mate i x)=x := by
  decide +kernel

theorem in385_trap_mate_cut_certificate : ∀ a b : Fin 15,
    (in385_trap_cut a b).Nonempty ∧ in385_trap_cut a b≠univ ∧
      ∀ x : Fin 15,
        (in385_trap_swap_block a b x∈in385_trap_cut a b ↔
          in385_trap_swap_block a b (in385_trap_mate (in385_trap_color a b) x)∈in385_trap_cut a b) := by
  decide +kernel

theorem in385_trap_swap_cut_certificate : ∀ a b : Fin 15,
    (in385_trap_cut a b).Nonempty ∧ in385_trap_cut a b≠univ ∧
      ∀ x y : Fin 15,x≠y → in385_trap_array x y=in385_trap_color a b →
        (in385_trap_swap_block a b x∈in385_trap_cut a b ↔
          in385_trap_swap_block a b y∈in385_trap_cut a b) := by
  intro a b
  refine ⟨(in385_trap_mate_cut_certificate a b).1,
    (in385_trap_mate_cut_certificate a b).2.1,?_⟩
  intro x y _ hA
  have hy : y=in385_trap_mate (in385_trap_color a b) x :=
    in385_trap_normalized.2.2 x (hA.trans (in385_trap_mate_color _ x).symm)
  rw [hy]
  exact (in385_trap_mate_cut_certificate a b).2.2 x

theorem wild_partition_single_swap_obstruction :
    (∀ a,in385_trap_array a a=a) ∧
    (∀ a b,in385_trap_array a b=in385_trap_array b a) ∧
    (∀ a,Function.Injective (in385_trap_array a)) ∧
    (∀ b : Fin 5,(univ.filter fun v => in385_trap_block v=b).card=3) ∧
    (∀ i x y : Fin 15,x≠y → in385_trap_block x=in385_trap_block i →
      in385_trap_block y=in385_trap_block i → in385_trap_array x y≠i) ∧
    (∀ a b : Fin 15,∃ i : Fin 15,
      wild_joint_bad_relation 5 (in385_trap_swap_block a b)
        (fun x y => x≠y ∧ in385_trap_array x y=i)) := by
  refine ⟨in385_trap_normalized.1,in385_trap_normalized.2.1,
    in385_trap_normalized.2.2,in385_trap_blocks_card,in385_trap_valid,?_⟩
  intro a b
  refine ⟨in385_trap_color a b,in385_trap_cut a b,
    (in385_trap_swap_cut_certificate a b).1,(in385_trap_swap_cut_certificate a b).2.1,?_⟩
  intro x y hxy
  exact (in385_trap_swap_cut_certificate a b).2.2 x y hxy.1 hxy.2
