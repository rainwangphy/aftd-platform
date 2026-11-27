import AFTD.Prelude

/-!
# op874_fixed_owner_obstruction_witness

Topic: graphs   Node: d3636f751e76

Provenance: helper lemma. Explicit finite witness for the fixed-owner obstruction of OP-874; experiments 43171–43177.

The explicit fourteen-vertex simple cubic graph, perfect matching and exact low-port ownership admit the compatible six-color local state required by the fixed-owner obstruction, with the specified exposed port using color 5.
-/

namespace IN1258OwnerWitness
def L : Fin 21 → Fin 14 := ![0,0,0,1,1,1,2,2,2,3,3,4,4,5,5,6,6,7,8,9,11]
def R : Fin 21 → Fin 14 := ![3,7,10,4,5,8,7,9,10,10,13,8,11,6,12,9,13,11,12,12,13]
def ends (e : Fin 21) : Sym2 (Fin 14) := s(L e,R e)
def in1258_match : Finset (Fin 21) := {2,3,7,10,13,17,18}
def in1258_bit : Fin 14 → Bool := ![false,true,true,true,true,false,false,false,false,true,false,false,false,true]
def own : Fin 14 → Fin 21 := ![1,4,8,9,3,13,16,6,18,7,2,17,14,10]
def c : Fin 21 → Fin 6 := ![2,5,0,1,5,3,4,1,3,5,1,2,3,0,4,3,4,0,0,2,2]
def hl : Fin 21 → Fin 6 := ![3,1,4,4,0,2,2,5,0,0,3,4,5,1,3,5,1,2,1,5,5]
def hr : Fin 21 → Fin 6 := ![4,3,1,0,2,4,1,0,2,4,0,5,4,2,1,4,5,1,5,3,3]
def h (v : Fin 14) (e : Fin 21) : Fin 6 := if v = L e then hl e else if v = R e then hr e else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem external_distinct : ∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → c e ≠ c f := by
  intro v
  fin_cases v <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hidden_distinct : ∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → h v e ≠ h v f := by
  intro v
  fin_cases v <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem local_disjoint : ∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → h v e ≠ c f := by
  intro v
  fin_cases v <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cross_disjoint : ∀ e f in1258_g, L e ∈ ends f → R e ∈ ends in1258_g → f ≠ e → in1258_g ≠ e → h (L e) f ≠ h (R e) in1258_g := by
  intro e
  fin_cases e <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem matching_colors : ∀ e ∈ in1258_match, c e = if in1258_bit (L e) then 1 else 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_colors : ∀ e ∉ in1258_match, 2 ≤ (c e).val := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem owner_hidden : ∀ v : Fin 14, h v (own v) = if in1258_bit v then 0 else 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem global_pair : ∀ e ∉ in1258_match, e ≠ own (L e) → e ≠ own (R e) → c e = 2 ∨ c e = 3 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem target_bad : h 6 15 = 5 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_double_owner : ∀ e : Fin 21, ¬ (own (L e) = e ∧ own (R e) = e) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exact_matching_owner : ∀ e ∈ in1258_match, (own (L e) = e ∨ own (R e) = e) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem owner_incident : ∀ v : Fin 14, v ∈ ends (own v) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_loops : ∀ e : Fin 21, L e ≠ R e := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_parallel : ∀ e f : Fin 21, ends e = ends f → e = f := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem degree_three : ∀ v : Fin 14, ((Finset.univ : Finset (Fin 21)).filter fun e => v ∈ ends e).card = 3 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem perfect_matching : ∀ v : Fin 14, ((Finset.univ : Finset (Fin 21)).filter fun e => e ∈ in1258_match ∧ v ∈ ends e).card = 1 := by decide

end IN1258OwnerWitness

theorem op874_fixed_owner_obstruction_witness :
  let L : Fin 21 → Fin 14 := ![0,0,0,1,1,1,2,2,2,3,3,4,4,5,5,6,6,7,8,9,11]
  let R : Fin 21 → Fin 14 := ![3,7,10,4,5,8,7,9,10,10,13,8,11,6,12,9,13,11,12,12,13]
  let ends : Fin 21 → Sym2 (Fin 14) := fun e => s(L e,R e)
  let in1258_match : Finset (Fin 21) := {2,3,7,10,13,17,18}
  let in1258_bit : Fin 14 → Bool := ![false,true,true,true,true,false,false,false,false,true,false,false,false,true]
  let own : Fin 14 → Fin 21 := ![1,4,8,9,3,13,16,6,18,7,2,17,14,10]
  ∃ (c : Fin 21 → Fin 6) (h : Fin 14 → Fin 21 → Fin 6),
  (
    (∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → c e ≠ c f) ∧
    (∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → e ≠ f → h v e ≠ h v f) ∧
    (∀ v : Fin 14, ∀ e f, v ∈ ends e → v ∈ ends f → h v e ≠ c f) ∧
    (∀ e f in1258_g, L e ∈ ends f → R e ∈ ends in1258_g → f ≠ e → in1258_g ≠ e → h (L e) f ≠ h (R e) in1258_g) ∧
    (∀ e ∈ in1258_match, c e = if in1258_bit (L e) then 1 else 0) ∧
    (∀ e ∉ in1258_match, 2 ≤ (c e).val) ∧
    (∀ v : Fin 14, h v (own v) = if in1258_bit v then 0 else 1) ∧
    (∀ e ∉ in1258_match, e ≠ own (L e) → e ≠ own (R e) → c e = 2 ∨ c e = 3)) ∧
    h 6 15 = 5 ∧
    (∀ e : Fin 21, ¬ (own (L e) = e ∧ own (R e) = e)) ∧
    (∀ e ∈ in1258_match, own (L e) = e ∨ own (R e) = e) ∧
    (∀ v : Fin 14, v ∈ ends (own v)) ∧
    (∀ e : Fin 21, L e ≠ R e) ∧
    (∀ e f : Fin 21, ends e = ends f → e = f) ∧
    (∀ v : Fin 14, ((Finset.univ : Finset (Fin 21)).filter fun e => v ∈ ends e).card = 3) ∧
    (∀ v : Fin 14, ((Finset.univ : Finset (Fin 21)).filter fun e => e ∈ in1258_match ∧ v ∈ ends e).card = 1) := by
  dsimp only
  refine ⟨IN1258OwnerWitness.c, IN1258OwnerWitness.h, ?_⟩
  exact ⟨⟨IN1258OwnerWitness.external_distinct, IN1258OwnerWitness.hidden_distinct,
    IN1258OwnerWitness.local_disjoint, IN1258OwnerWitness.cross_disjoint,
    IN1258OwnerWitness.matching_colors, IN1258OwnerWitness.factor_colors,
    IN1258OwnerWitness.owner_hidden, IN1258OwnerWitness.global_pair⟩,
    IN1258OwnerWitness.target_bad, IN1258OwnerWitness.no_double_owner,
    IN1258OwnerWitness.exact_matching_owner, IN1258OwnerWitness.owner_incident,
    IN1258OwnerWitness.no_loops, IN1258OwnerWitness.no_parallel,
    IN1258OwnerWitness.degree_three, IN1258OwnerWitness.perfect_matching⟩
