import AFTD.Prelude
import AFTD.Kb.Tcs.Op874DefectFreeProducerFiveCycleImpossible

/-!
# op874_defect_free_producer_forces_square_word

Topic: graphs   Node: 013b2eafb5c5

Provenance: helper lemma. Defect-free producer-cycle reduction associated with experiment 35807.

On any cycle of length at least three, the fixed producer orientation with no defects and the stated local and interface constraints forces the four high factor-edge colors to be proper at distances one and two.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
open In1081NoDefectFive

theorem op874_defect_free_producer_forces_square_word
    (n : ℕ) [NeZero n] (hn : 3 ≤ n) (c p q : Fin n → Fin 4)
    (hlocal : ∀ i, [c (i-1), c i, p i, q i].Nodup)
    (hcross : ∀ i, q i ≠ p (i+1) ∧ q i ≠ q (i+1)) :
    ∀ i, c i ≠ c (i+1) ∧ c i ≠ c (i+2) := by
  have hone : (1 : Fin n).val = 1 := by
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have htwo : (2 : Fin n).val = 2 := by
    change 2 % n = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hsum : (1 : Fin n)+1 = 2 := by
    apply Fin.ext
    rw [Fin.val_add, hone, htwo, Nat.mod_eq_of_lt (by omega : 2<n)]
  have qeq (i : Fin n) : q i = c (i+1) := by
    have h := hlocal (i+1)
    simp only [add_sub_cancel_right, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, not_or, List.nodup_nil, not_false_eq_true, and_true] at h
    have hi := hlocal i
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil,
      List.not_mem_nil, not_false_eq_true, and_true] at hi
    exact fourth_color (c i) (c (i+1)) (p (i+1)) (q (i+1)) (q i)
      h.1.1 h.1.2.1 h.1.2.2 h.2.1.1 h.2.1.2 h.2.2
      (Ne.symm hi.2.1.2) (hcross i).1 (hcross i).2
  intro i
  constructor
  · have h := hlocal (i+1)
    simp only [add_sub_cancel_right, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, not_or, List.nodup_nil, not_false_eq_true, and_true] at h
    exact h.1.1
  · intro he
    have h := hlocal (i+1)
    simp only [add_sub_cancel_right, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, not_or, List.nodup_nil, not_false_eq_true, and_true] at h
    have hq := qeq (i+1)
    have hq' : q (i+1) = c (i+2) := by simpa [add_assoc, hsum] using hq
    exact h.1.2.2 (he.trans hq'.symm)
