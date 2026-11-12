import AFTD.Prelude

/-!
# op_1370_blocked_witness_minor_counterexample

Topic: combinatorics   Node: b058591cf43b

Provenance: helper lemma. Counterexample to a fixed-witness blocked-matrix rank shortcut for arXiv:2611.12199, Conjecture 4.3. Masks encode subsets of Fin 4 in binary.

For the two singleton families represented by masks 10 and 12 on four elements, mask 3 is incomparable to both. If one retains precisely the complement orbits for which both orientations are comparable to one of those two sets, then the principal matrix on masks 10, 12, and 3 has rows (1,0,1), (0,1,0), and (1,0,1), for any diagonal weights q. Thus the principal extension by this particular incomparable witness is singular.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

abbrev op1370_mask_sub (a b : ℕ) : Prop := (a &&& b) = a

abbrev op1370_mask_inc (a b : ℕ) : Prop := ¬ op1370_mask_sub a b ∧ ¬ op1370_mask_sub b a

abbrev op1370_blocked (c : ℕ) : Prop :=
  ¬ (op1370_mask_inc c 10 ∧ op1370_mask_inc c 12) ∧
  ¬ (op1370_mask_inc (15 - c) 10 ∧ op1370_mask_inc (15 - c) 12)

def op1370_mask_parity (a c : ℕ) : ℚ :=
  if ((Finset.range 4).filter (fun i => Nat.testBit c i ≠ Nat.testBit a i)).card % 2 = 0 then 1 else -1

def op1370_mask_weight (c : ℕ) : ℚ := if c < 8 then 2 else 1 / 2

def op1370_blocked_entry (q : ℕ → ℚ) (a b : ℕ) : ℚ :=
  ∑ c : Fin 16, if op1370_blocked c.val ∧ op1370_mask_sub a c.val then
    op1370_mask_parity a c.val *
      ((if op1370_mask_sub c.val b then q c.val else 0) +
       (if op1370_mask_sub (15 - c.val) b then 1 else 0))
  else 0


def op1370_mask_index : Fin 3 → ℕ := ![10, 12, 3]

lemma op1370_no_diagonal_term : ∀ i j : Fin 3, ∀ c : Fin 16,
    ¬ (op1370_blocked c.val ∧ op1370_mask_sub (op1370_mask_index i) c.val ∧
      op1370_mask_sub c.val (op1370_mask_index j)) := by decide +kernel

lemma op1370_entry_irrelevant (q : ℕ → ℚ) (i j : Fin 3) :
    op1370_blocked_entry q (op1370_mask_index i) (op1370_mask_index j) =
      op1370_blocked_entry (fun _ => 0) (op1370_mask_index i) (op1370_mask_index j) := by
  unfold op1370_blocked_entry
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : op1370_blocked c.val ∧ op1370_mask_sub (op1370_mask_index i) c.val
  · have no : ¬ op1370_mask_sub c.val (op1370_mask_index j) := by
      intro hc
      exact op1370_no_diagonal_term i j c ⟨h.1, h.2, hc⟩
    simp [h, no]
  · simp [h]
lemma op1370_blocked_witness_inc : op1370_mask_inc 10 12 ∧ op1370_mask_inc 3 10 ∧ op1370_mask_inc 3 12 := by decide +kernel

theorem op_1370_blocked_witness_minor_counterexample (q : ℕ → ℚ) :
  (op1370_mask_inc 10 12 ∧ op1370_mask_inc 3 10 ∧ op1370_mask_inc 3 12) ∧
  (
    op1370_blocked_entry q 10 10 = 1 ∧ op1370_blocked_entry q 10 12 = 0 ∧
    op1370_blocked_entry q 10 3 = 1 ∧ op1370_blocked_entry q 12 10 = 0 ∧
    op1370_blocked_entry q 12 12 = 1 ∧ op1370_blocked_entry q 12 3 = 0 ∧
    op1370_blocked_entry q 3 10 = 1 ∧ op1370_blocked_entry q 3 12 = 0 ∧
    op1370_blocked_entry q 3 3 = 1) := by
  refine ⟨op1370_blocked_witness_inc, ?_⟩
  have h00 := op1370_entry_irrelevant q 0 0
  have h01 := op1370_entry_irrelevant q 0 1
  have h02 := op1370_entry_irrelevant q 0 2
  have h10 := op1370_entry_irrelevant q 1 0
  have h11 := op1370_entry_irrelevant q 1 1
  have h12 := op1370_entry_irrelevant q 1 2
  have h20 := op1370_entry_irrelevant q 2 0
  have h21 := op1370_entry_irrelevant q 2 1
  have h22 := op1370_entry_irrelevant q 2 2
  simp only [op1370_mask_index, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at *
  change op1370_blocked_entry q 10 3 = op1370_blocked_entry (fun _ => 0) 10 3 at h02
  change op1370_blocked_entry q 12 3 = op1370_blocked_entry (fun _ => 0) 12 3 at h12
  change op1370_blocked_entry q 3 10 = op1370_blocked_entry (fun _ => 0) 3 10 at h20
  change op1370_blocked_entry q 3 12 = op1370_blocked_entry (fun _ => 0) 3 12 at h21
  change op1370_blocked_entry q 3 3 = op1370_blocked_entry (fun _ => 0) 3 3 at h22
  rw [h00,h01,h02,h10,h11,h12,h20,h21,h22]
  decide +kernel
