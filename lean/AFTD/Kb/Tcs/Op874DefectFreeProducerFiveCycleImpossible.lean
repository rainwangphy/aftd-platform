import AFTD.Prelude

/-!
# op874_defect_free_producer_five_cycle_impossible

Topic: graphs   Node: 871dd1b4ba98

Provenance: helper lemma. Fixed-orientation producer-cycle obstruction, experiment 35807.

A defect-free producer five-cycle cannot satisfy the four-high-color local and adjacent interface constraints in the fixed producer orientation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081NoDefectFive
theorem fourth_color (a b x y z : Fin 4)
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hza : z ≠ a) (hzx : z ≠ x) (hzy : z ≠ y) : z = b := by
  by_contra hzb
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hax' : a.val ≠ x.val := fun h => hax (Fin.ext h)
  have hay' : a.val ≠ y.val := fun h => hay (Fin.ext h)
  have hbx' : b.val ≠ x.val := fun h => hbx (Fin.ext h)
  have hby' : b.val ≠ y.val := fun h => hby (Fin.ext h)
  have hxy' : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have hza' : z.val ≠ a.val := fun h => hza (Fin.ext h)
  have hzb' : z.val ≠ b.val := fun h => hzb (Fin.ext h)
  have hzx' : z.val ≠ x.val := fun h => hzx (Fin.ext h)
  have hzy' : z.val ≠ y.val := fun h => hzy (Fin.ext h)
  have := a.isLt; have := b.isLt; have := x.isLt; have := y.isLt; have := z.isLt
  omega

end In1081NoDefectFive

theorem op874_defect_free_producer_five_cycle_impossible (c p q : Fin 5 → Fin 4)
    (hlocal : ∀ i, [c (i-1), c i, p i, q i].Nodup)
    (hcross : ∀ i, q i ≠ p (i+1) ∧ q i ≠ q (i+1)) : False := by
  have qeq (i : Fin 5) : q i = c (i+1) := by
    have h := hlocal (i+1)
    simp only [add_sub_cancel_right, List.nodup_cons, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, not_or, List.nodup_nil, List.not_mem_nil, not_false_eq_true, and_true] at h
    have hi := hlocal i
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      not_or, List.nodup_nil, List.not_mem_nil, not_false_eq_true, and_true] at hi
    exact In1081NoDefectFive.fourth_color (c i) (c (i+1)) (p (i+1)) (q (i+1)) (q i)
      h.1.1 h.1.2.1 h.1.2.2 h.2.1.1 h.2.1.2 h.2.2
      (Ne.symm hi.2.1.2) (hcross i).1 (hcross i).2
  have hnear : ∀ i, c i ≠ c (i+1) := by
    intro i
    have h := hlocal (i+1)
    simp only [add_sub_cancel_right, List.nodup_cons, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, not_or, List.nodup_nil, List.not_mem_nil, not_false_eq_true, and_true] at h
    exact h.1.1
  have hfar : ∀ i, c i ≠ c (i+2) := by
    intro i he
    have h := hlocal (i+1)
    simp only [add_sub_cancel_right, List.nodup_cons, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, not_or, List.nodup_nil, List.not_mem_nil, not_false_eq_true, and_true] at h
    have hq := qeq (i+1)
    have hs : (1 : Fin 5)+1 = 2 := by decide
    have hq' : q (i+1) = c (i+2) := by simpa [add_assoc, hs] using hq
    exact h.1.2.2 (he.trans hq'.symm)
  have hcover : ∀ i j : Fin 5, i ≠ j →
      j = i+1 ∨ j = i+2 ∨ i = j+1 ∨ i = j+2 := by decide
  have hinj : Function.Injective c := by
    intro i j he
    by_contra hij
    rcases hcover i j hij with h | h | h | h
    · exact hnear i (by simpa [h] using he)
    · exact hfar i (by simpa [h] using he)
    · exact hnear j (by simpa [h] using he.symm)
    · exact hfar j (by simpa [h] using he.symm)
  have hc := Fintype.card_le_of_injective c hinj
  norm_num at hc
