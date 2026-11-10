import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingReverseCrossoutValid
import AFTD.Kb.GameTheoryEconomics.PickingReverseCrossoutAllocation
import AFTD.Kb.GameTheoryEconomics.BlockSnakeSeqTwo
import AFTD.Kb.GameTheoryEconomics.IsNelPd
import AFTD.Kb.GameTheoryEconomics.IsEf1Pd

/-!
# block_snake_reverse_crossout_nel_ef1

Topic: fair_division   Node: 9041c8e8de49

Provenance: helper lemma. Reverse crossout representation of two-agent sequential picking; see https://cdn.aaai.org/ojs/8697/8697-13-12225-1-2-20201228.pdf Theorem 1.

For any two real item-value functions and any valid reverse crossout sequence for the two-agent block-snake picking order, the resulting allocation satisfies NEL and EF1 under the item relations induced by those values.
-/

/-- Position of agent 0's `i`-th item in the reversed block-snake order. -/
def block_snake_reverse_crossout_nel_ef1_A (k : ℕ) (i : Fin k) : Fin (2*k+1) := ⟨2*i.val + 2, by omega⟩

/-- Position of agent 1's `j`-th item in the reversed block-snake order. -/
def block_snake_reverse_crossout_nel_ef1_B (k : ℕ) (j : Fin (k+1)) : Fin (2*k+1) :=
  if h : j.val = 0 then ⟨0, by omega⟩ else ⟨2*j.val - 1, by have := j.isLt; omega⟩

/-- The last index of `Fin k`. -/
def block_snake_reverse_crossout_nel_ef1_last (k : ℕ) (hk : 0 < k) : Fin k := ⟨k-1, by omega⟩

/-- Deleting the entry `m` from the ordered list `0,1,...,k` of `Fin (k+1)`. -/
def block_snake_reverse_crossout_nel_ef1_T (k : ℕ) (hk : 0 < k) (m : Fin (k+1))
    (j : Fin (k+1)) : Fin k :=
  if h0 : j.val = 0 then ⟨0, hk⟩
  else if h1 : j.val < m.val then ⟨j.val, by have := j.isLt; omega⟩
  else if h2 : j.val = m.val then ⟨0, hk⟩
  else ⟨j.val - 1, by have := j.isLt; omega⟩

/-- A left inverse of `block_snake_reverse_crossout_nel_ef1_T` outside `m`. -/
def block_snake_reverse_crossout_nel_ef1_Tinv (k : ℕ) (hk : 0 < k) (m : Fin (k+1))
    (i : Fin k) : Fin (k+1) :=
  ⟨if i.val < m.val then i.val else i.val + 1, by have := i.isLt; split <;> omega⟩

/-- Insertion of `i` back into the ordered list `0,1,...,k` with the last entry `k` omitted. -/
def block_snake_reverse_crossout_nel_ef1_T2 (k : ℕ) (hk : 0 < k) (i : Fin k) : Fin (k+1) :=
  if h : i.val < k-1 then ⟨i.val+2, by have := i.isLt; omega⟩ else ⟨0, by omega⟩

/-- The index of an item among agent 1's picks, when it is one of them. -/
noncomputable def block_snake_reverse_crossout_nel_ef1_J (k : ℕ)
    (π : Fin (2*k+1) → Fin (2*k+1)) (z : Fin (2*k+1)) : Fin (k+1) :=
  if h : ∃ j : Fin (k+1), π (block_snake_reverse_crossout_nel_ef1_B k j) = z then h.choose else 0

/-- The index of an item among agent 0's picks, when it is one of them. -/
noncomputable def block_snake_reverse_crossout_nel_ef1_I (k : ℕ) (d : Fin k)
    (π : Fin (2*k+1) → Fin (2*k+1)) (z : Fin (2*k+1)) : Fin k :=
  if h : ∃ i : Fin k, π (block_snake_reverse_crossout_nel_ef1_A k i) = z then h.choose else d

/-- The NEL injection out of agent 1's bundle with one item deleted. -/
noncomputable def block_snake_reverse_crossout_nel_ef1_F0 (k : ℕ) (hk : 0 < k)
    (π : Fin (2*k+1) → Fin (2*k+1)) (y z : Fin (2*k+1)) : Fin (2*k+1) :=
  π (block_snake_reverse_crossout_nel_ef1_A k
    (block_snake_reverse_crossout_nel_ef1_T k hk (block_snake_reverse_crossout_nel_ef1_J k π y)
      (block_snake_reverse_crossout_nel_ef1_J k π z)))

/-- The EF1 injection out of agent 0's bundle with its last item deleted. -/
noncomputable def block_snake_reverse_crossout_nel_ef1_F1 (k : ℕ) (hk : 0 < k)
    (π : Fin (2*k+1) → Fin (2*k+1)) (z : Fin (2*k+1)) : Fin (2*k+1) :=
  π (block_snake_reverse_crossout_nel_ef1_B k
    (block_snake_reverse_crossout_nel_ef1_T2 k hk
      (block_snake_reverse_crossout_nel_ef1_I k (block_snake_reverse_crossout_nel_ef1_last k hk) π z)))

theorem block_snake_reverse_crossout_nel_ef1_J_spec (k : ℕ) (π : Fin (2*k+1) → Fin (2*k+1))
    (z : Fin (2*k+1))
    (h : ∃ j : Fin (k+1), π (block_snake_reverse_crossout_nel_ef1_B k j) = z) :
    π (block_snake_reverse_crossout_nel_ef1_B k
      (block_snake_reverse_crossout_nel_ef1_J k π z)) = z := by
  rw [block_snake_reverse_crossout_nel_ef1_J, dif_pos h]; exact Classical.choose_spec h

theorem block_snake_reverse_crossout_nel_ef1_I_spec (k : ℕ) (d : Fin k)
    (π : Fin (2*k+1) → Fin (2*k+1)) (z : Fin (2*k+1))
    (h : ∃ i : Fin k, π (block_snake_reverse_crossout_nel_ef1_A k i) = z) :
    π (block_snake_reverse_crossout_nel_ef1_A k
      (block_snake_reverse_crossout_nel_ef1_I k d π z)) = z := by
  rw [block_snake_reverse_crossout_nel_ef1_I, dif_pos h]; exact Classical.choose_spec h

theorem block_snake_reverse_crossout_nel_ef1_A_inj (k : ℕ) :
    Function.Injective (block_snake_reverse_crossout_nel_ef1_A k) := by
  intro i i' h
  simp only [block_snake_reverse_crossout_nel_ef1_A, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

theorem block_snake_reverse_crossout_nel_ef1_B_inj (k : ℕ) :
    Function.Injective (block_snake_reverse_crossout_nel_ef1_B k) := by
  intro j j' h
  by_cases hj : j.val = 0
  · by_cases hj' : j'.val = 0
    · exact Fin.ext (by omega)
    · simp [block_snake_reverse_crossout_nel_ef1_B, hj, hj'] at h; omega
  · by_cases hj' : j'.val = 0
    · simp [block_snake_reverse_crossout_nel_ef1_B, hj, hj'] at h; omega
    · simp [block_snake_reverse_crossout_nel_ef1_B, hj, hj'] at h; exact Fin.ext (by omega)

theorem block_snake_reverse_crossout_nel_ef1_J_apply (k : ℕ) (π : Fin (2*k+1) → Fin (2*k+1))
    (hinj : Function.Injective π) (j : Fin (k+1)) :
    block_snake_reverse_crossout_nel_ef1_J k π
      (π (block_snake_reverse_crossout_nel_ef1_B k j)) = j := by
  have hex : ∃ j' : Fin (k+1),
      π (block_snake_reverse_crossout_nel_ef1_B k j') =
        π (block_snake_reverse_crossout_nel_ef1_B k j) := ⟨j, rfl⟩
  rw [block_snake_reverse_crossout_nel_ef1_J, dif_pos hex]
  exact hinj.comp (block_snake_reverse_crossout_nel_ef1_B_inj k) (Classical.choose_spec hex)

theorem block_snake_reverse_crossout_nel_ef1_I_apply (k : ℕ) (d : Fin k)
    (π : Fin (2*k+1) → Fin (2*k+1)) (hinj : Function.Injective π) (i : Fin k) :
    block_snake_reverse_crossout_nel_ef1_I k d π
      (π (block_snake_reverse_crossout_nel_ef1_A k i)) = i := by
  have hex : ∃ i' : Fin k,
      π (block_snake_reverse_crossout_nel_ef1_A k i') =
        π (block_snake_reverse_crossout_nel_ef1_A k i) := ⟨i, rfl⟩
  rw [block_snake_reverse_crossout_nel_ef1_I, dif_pos hex]
  exact hinj.comp (block_snake_reverse_crossout_nel_ef1_A_inj k) (Classical.choose_spec hex)

theorem block_snake_reverse_crossout_nel_ef1_revGet (k : ℕ) (t : Fin (2*k+1)) :
    (block_snake_seq_two k).reverse.getD t.val 0 =
      (if t.val % 2 = 0 ∧ 0 < t.val then (0:Fin 2) else 1) := by
  simp only [block_snake_seq_two]
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse]
  · rw [List.length_ofFn, List.getElem?_ofFn]
    rw [dif_pos (by omega : 2*k+1-1-t.val < 2*k+1)]
    simp only [Option.getD_some]
    have hcond : ((2*k+1-1-t.val)%2=0 ∧ 2*k+1-1-t.val<2*k) ↔ (t.val%2=0 ∧ 0<t.val) := by omega
    rw [if_congr hcond rfl rfl]
  · rw [List.length_ofFn]; exact t.isLt

theorem block_snake_reverse_crossout_nel_ef1_revZero (k : ℕ) (t : Fin (2*k+1)) :
    (block_snake_seq_two k).reverse.getD t.val 0 = 0 ↔ t.val % 2 = 0 ∧ 0 < t.val := by
  rw [block_snake_reverse_crossout_nel_ef1_revGet]
  by_cases h : t.val % 2 = 0 ∧ 0 < t.val <;> simp [h]

theorem block_snake_reverse_crossout_nel_ef1_revOne (k : ℕ) (t : Fin (2*k+1)) :
    (block_snake_seq_two k).reverse.getD t.val 0 = 1 ↔ ¬(t.val % 2 = 0 ∧ 0 < t.val) := by
  rw [block_snake_reverse_crossout_nel_ef1_revGet]
  by_cases h : t.val % 2 = 0 ∧ 0 < t.val <;> simp [h]

theorem block_snake_reverse_crossout_nel_ef1_Azero (k : ℕ) (i : Fin k) :
    (block_snake_seq_two k).reverse.getD (block_snake_reverse_crossout_nel_ef1_A k i).val 0 = 0 := by
  rw [block_snake_reverse_crossout_nel_ef1_revZero]
  simp only [block_snake_reverse_crossout_nel_ef1_A, Fin.val_mk]; omega

theorem block_snake_reverse_crossout_nel_ef1_Bone (k : ℕ) (j : Fin (k+1)) :
    (block_snake_seq_two k).reverse.getD (block_snake_reverse_crossout_nel_ef1_B k j).val 0 = 1 := by
  rw [block_snake_reverse_crossout_nel_ef1_revOne]
  intro h
  simp only [block_snake_reverse_crossout_nel_ef1_B] at h
  split_ifs at h with hj <;> simp at h <;> omega

theorem block_snake_reverse_crossout_nel_ef1_existsA (k : ℕ) (t : Fin (2*k+1))
    (h1 : t.val % 2 = 0) (h2 : 0 < t.val) :
    ∃ i : Fin k, block_snake_reverse_crossout_nel_ef1_A k i = t := by
  have hev : Even t.val := Nat.even_iff.mpr h1
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp hev
  refine ⟨⟨m-1, ?_⟩, ?_⟩
  · have := t.isLt; omega
  · apply Fin.ext; simp [block_snake_reverse_crossout_nel_ef1_A]; omega

theorem block_snake_reverse_crossout_nel_ef1_existsB (k : ℕ) (t : Fin (2*k+1))
    (h : ¬(t.val % 2 = 0 ∧ 0 < t.val)) :
    ∃ j : Fin (k+1), block_snake_reverse_crossout_nel_ef1_B k j = t := by
  by_cases ht0 : t.val = 0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    apply Fin.ext; simp [block_snake_reverse_crossout_nel_ef1_B, ht0]
  · have hodd : t.val % 2 = 1 := by have := Nat.mod_two_eq_zero_or_one t.val; omega
    have hodd' : Odd t.val := Nat.odd_iff.mpr hodd
    obtain ⟨b, hb⟩ := odd_iff_exists_bit1.mp hodd'
    refine ⟨⟨b+1, by have := t.isLt; omega⟩, ?_⟩
    apply Fin.ext
    simp only [block_snake_reverse_crossout_nel_ef1_B]
    have hb1 : b + 1 ≠ 0 := by omega
    rw [dif_neg hb1]
    show 2 * (b + 1) - 1 = t.val
    omega

theorem block_snake_reverse_crossout_nel_ef1_allocZero (k : ℕ) (p : Fin (2*k+1) → Fin (2*k+1)) :
    picking_reverse_crossout_allocation (block_snake_seq_two k) p 0
      = Finset.univ.image (fun i : Fin k => p (block_snake_reverse_crossout_nel_ef1_A k i)) := by
  ext z
  simp only [picking_reverse_crossout_allocation, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [block_snake_reverse_crossout_nel_ef1_revZero] at ht
    obtain ⟨i, hi⟩ := block_snake_reverse_crossout_nel_ef1_existsA k t ht.1 ht.2
    exact ⟨i, by rw [hi]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨block_snake_reverse_crossout_nel_ef1_A k i,
      block_snake_reverse_crossout_nel_ef1_Azero k i, rfl⟩

theorem block_snake_reverse_crossout_nel_ef1_allocOne (k : ℕ) (p : Fin (2*k+1) → Fin (2*k+1)) :
    picking_reverse_crossout_allocation (block_snake_seq_two k) p 1
      = Finset.univ.image (fun j : Fin (k+1) => p (block_snake_reverse_crossout_nel_ef1_B k j)) := by
  ext z
  simp only [picking_reverse_crossout_allocation, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [block_snake_reverse_crossout_nel_ef1_revOne] at ht
    obtain ⟨j, hj⟩ := block_snake_reverse_crossout_nel_ef1_existsB k t ht
    exact ⟨j, by rw [hj]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨block_snake_reverse_crossout_nel_ef1_B k j,
      block_snake_reverse_crossout_nel_ef1_Bone k j, rfl⟩

theorem block_snake_reverse_crossout_nel_ef1_cardZero (k : ℕ) (p : Fin (2*k+1) → Fin (2*k+1))
    (hp : Function.Injective p) :
    (picking_reverse_crossout_allocation (block_snake_seq_two k) p 0).card = k := by
  rw [block_snake_reverse_crossout_nel_ef1_allocZero, Finset.card_image_of_injective]
  · simp
  · exact hp.comp (block_snake_reverse_crossout_nel_ef1_A_inj k)

theorem block_snake_reverse_crossout_nel_ef1_cardOne (k : ℕ) (p : Fin (2*k+1) → Fin (2*k+1))
    (hp : Function.Injective p) :
    (picking_reverse_crossout_allocation (block_snake_seq_two k) p 1).card = k+1 := by
  rw [block_snake_reverse_crossout_nel_ef1_allocOne, Finset.card_image_of_injective]
  · simp
  · exact hp.comp (block_snake_reverse_crossout_nel_ef1_B_inj k)

theorem block_snake_reverse_crossout_nel_ef1_minZero (k : ℕ)
    (u : Fin 2 → Fin (2*k+1) → ℝ) (π : Fin (2*k+1) → Fin (2*k+1))
    (hmin : ∀ t j : Fin (2*k+1), t < j →
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π t) ≤
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π j))
    {t t' : Fin (2*k+1)} (hlt : t < t')
    (hP : (block_snake_seq_two k).reverse.getD t.val 0 = 1) :
    u 0 (π t) ≤ u 0 (π t') := by
  have h := hmin t t' hlt
  rw [hP] at h
  simpa using h

theorem block_snake_reverse_crossout_nel_ef1_minOne (k : ℕ)
    (u : Fin 2 → Fin (2*k+1) → ℝ) (π : Fin (2*k+1) → Fin (2*k+1))
    (hmin : ∀ t j : Fin (2*k+1), t < j →
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π t) ≤
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π j))
    {t t' : Fin (2*k+1)} (hlt : t < t')
    (hP : (block_snake_seq_two k).reverse.getD t.val 0 = 0) :
    u 1 (π t) ≤ u 1 (π t') := by
  have h := hmin t t' hlt
  rw [hP] at h
  simpa using h

theorem block_snake_reverse_crossout_nel_ef1_TinvT (k : ℕ) (hk : 0 < k) (m : Fin (k+1))
    (j : Fin (k+1)) (hj : j ≠ m) :
    block_snake_reverse_crossout_nel_ef1_Tinv k hk m
      (block_snake_reverse_crossout_nel_ef1_T k hk m j) = j := by
  by_cases h0 : j.val = 0
  · have hm : 0 < m.val := by
      have : m.val ≠ 0 := by intro h; exact hj (Fin.ext (by omega))
      omega
    rw [block_snake_reverse_crossout_nel_ef1_T]; rw [dif_pos h0]
    apply Fin.ext
    simp only [block_snake_reverse_crossout_nel_ef1_Tinv, Fin.val_mk]
    rw [if_pos hm]
    exact h0.symm
  · by_cases hlt : j.val < m.val
    · rw [block_snake_reverse_crossout_nel_ef1_T]; rw [dif_neg h0]; rw [dif_pos hlt]
      apply Fin.ext
      simp only [block_snake_reverse_crossout_nel_ef1_Tinv, Fin.val_mk]
      rw [if_pos hlt]
    · have hgt : m.val < j.val := by
        have : m.val ≠ j.val := by intro h; exact hj (Fin.ext (by omega))
        omega
      rw [block_snake_reverse_crossout_nel_ef1_T]; rw [dif_neg h0]; rw [dif_neg hlt]
      rw [dif_neg (by omega : ¬ j.val = m.val)]
      apply Fin.ext
      simp only [block_snake_reverse_crossout_nel_ef1_Tinv, Fin.val_mk]
      rw [if_neg (by omega : ¬ j.val - 1 < m.val)]
      omega

theorem block_snake_reverse_crossout_nel_ef1_T_inj (k : ℕ) (hk : 0 < k) (m : Fin (k+1))
    {j1 j2 : Fin (k+1)} (h1 : j1 ≠ m) (h2 : j2 ≠ m)
    (he : block_snake_reverse_crossout_nel_ef1_T k hk m j1 =
      block_snake_reverse_crossout_nel_ef1_T k hk m j2) : j1 = j2 := by
  have e1 := block_snake_reverse_crossout_nel_ef1_TinvT k hk m j1 h1
  have e2 := block_snake_reverse_crossout_nel_ef1_TinvT k hk m j2 h2
  rw [he] at e1
  rw [e1] at e2
  exact e2

theorem block_snake_reverse_crossout_nel_ef1_U0 (k : ℕ) (hk : 0 < k)
    (u : Fin 2 → Fin (2*k+1) → ℝ) (π : Fin (2*k+1) → Fin (2*k+1))
    (hmin : ∀ t j : Fin (2*k+1), t < j →
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π t) ≤
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π j))
    (m : Fin (k+1)) (j : Fin (k+1)) (hjm : j ≠ m) :
    u 0 (π (block_snake_reverse_crossout_nel_ef1_B k j)) ≤
      u 0 (π (block_snake_reverse_crossout_nel_ef1_A k
        (block_snake_reverse_crossout_nel_ef1_T k hk m j))) := by
  have hP : (block_snake_seq_two k).reverse.getD
      (block_snake_reverse_crossout_nel_ef1_B k j).val 0 = 1 :=
    block_snake_reverse_crossout_nel_ef1_Bone k j
  by_cases h0 : j.val = 0
  · have htgt : block_snake_reverse_crossout_nel_ef1_T k hk m j = ⟨0, hk⟩ := by
      rw [block_snake_reverse_crossout_nel_ef1_T]; rw [dif_pos h0]
    rw [htgt]
    apply block_snake_reverse_crossout_nel_ef1_minZero k u π hmin _ hP
    show (block_snake_reverse_crossout_nel_ef1_B k j).val <
      (block_snake_reverse_crossout_nel_ef1_A k ⟨0, hk⟩).val
    simp only [block_snake_reverse_crossout_nel_ef1_B, block_snake_reverse_crossout_nel_ef1_A]
    rw [dif_pos h0]; simp
  · by_cases hlt : j.val < m.val
    · have htgt : block_snake_reverse_crossout_nel_ef1_T k hk m j =
          ⟨j.val, by have := j.isLt; omega⟩ := by
        rw [block_snake_reverse_crossout_nel_ef1_T]; rw [dif_neg h0]; rw [dif_pos hlt]
      rw [htgt]
      apply block_snake_reverse_crossout_nel_ef1_minZero k u π hmin _ hP
      show (block_snake_reverse_crossout_nel_ef1_B k j).val <
        (block_snake_reverse_crossout_nel_ef1_A k ⟨j.val, by have := j.isLt; omega⟩).val
      simp only [block_snake_reverse_crossout_nel_ef1_B, block_snake_reverse_crossout_nel_ef1_A]
      rw [dif_neg h0]; simp; omega
    · have hgt : m.val < j.val := by
        have : m.val ≠ j.val := by intro h; exact hjm (Fin.ext (by omega))
        omega
      have htgt : block_snake_reverse_crossout_nel_ef1_T k hk m j =
          ⟨j.val - 1, by have := j.isLt; omega⟩ := by
        rw [block_snake_reverse_crossout_nel_ef1_T]; rw [dif_neg h0]; rw [dif_neg hlt]
        rw [dif_neg (by omega : ¬ j.val = m.val)]
      rw [htgt]
      apply block_snake_reverse_crossout_nel_ef1_minZero k u π hmin _ hP
      show (block_snake_reverse_crossout_nel_ef1_B k j).val <
        (block_snake_reverse_crossout_nel_ef1_A k ⟨j.val - 1, by have := j.isLt; omega⟩).val
      simp only [block_snake_reverse_crossout_nel_ef1_B, block_snake_reverse_crossout_nel_ef1_A]
      rw [dif_neg h0]; simp; omega

theorem block_snake_reverse_crossout_nel_ef1_ltLast (k : ℕ) (hk : 0 < k) (i : Fin k)
    (hi : i ≠ block_snake_reverse_crossout_nel_ef1_last k hk) : i.val < k-1 := by
  have h1 := i.isLt
  have h2 : i.val ≠ k-1 := by
    intro h
    apply hi
    apply Fin.ext
    simp only [block_snake_reverse_crossout_nel_ef1_last, Fin.val_mk]
    omega
  omega

theorem block_snake_reverse_crossout_nel_ef1_T2val (k : ℕ) (hk : 0 < k) (i : Fin k)
    (hi : i ≠ block_snake_reverse_crossout_nel_ef1_last k hk) :
    block_snake_reverse_crossout_nel_ef1_T2 k hk i =
      ⟨i.val+2, by have h := block_snake_reverse_crossout_nel_ef1_ltLast k hk i hi; omega⟩ := by
  rw [block_snake_reverse_crossout_nel_ef1_T2]
  rw [dif_pos (block_snake_reverse_crossout_nel_ef1_ltLast k hk i hi)]

theorem block_snake_reverse_crossout_nel_ef1_T2_inj (k : ℕ) (hk : 0 < k) {i1 i2 : Fin k}
    (h1 : i1 ≠ block_snake_reverse_crossout_nel_ef1_last k hk)
    (h2 : i2 ≠ block_snake_reverse_crossout_nel_ef1_last k hk)
    (he : block_snake_reverse_crossout_nel_ef1_T2 k hk i1 =
      block_snake_reverse_crossout_nel_ef1_T2 k hk i2) : i1 = i2 := by
  rw [block_snake_reverse_crossout_nel_ef1_T2val k hk i1 h1,
    block_snake_reverse_crossout_nel_ef1_T2val k hk i2 h2] at he
  apply Fin.ext
  simp only [Fin.mk.injEq] at he
  omega

theorem block_snake_reverse_crossout_nel_ef1_U1 (k : ℕ) (hk : 0 < k)
    (u : Fin 2 → Fin (2*k+1) → ℝ) (π : Fin (2*k+1) → Fin (2*k+1))
    (hmin : ∀ t j : Fin (2*k+1), t < j →
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π t) ≤
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π j))
    (i : Fin k) (hi : i ≠ block_snake_reverse_crossout_nel_ef1_last k hk) :
    u 1 (π (block_snake_reverse_crossout_nel_ef1_A k i)) ≤
      u 1 (π (block_snake_reverse_crossout_nel_ef1_B k
        (block_snake_reverse_crossout_nel_ef1_T2 k hk i))) := by
  have hP : (block_snake_seq_two k).reverse.getD
      (block_snake_reverse_crossout_nel_ef1_A k i).val 0 = 0 :=
    block_snake_reverse_crossout_nel_ef1_Azero k i
  rw [block_snake_reverse_crossout_nel_ef1_T2val k hk i hi]
  apply block_snake_reverse_crossout_nel_ef1_minOne k u π hmin _ hP
  show (block_snake_reverse_crossout_nel_ef1_A k i).val <
    (block_snake_reverse_crossout_nel_ef1_B k
      ⟨i.val+2, by have h := block_snake_reverse_crossout_nel_ef1_ltLast k hk i hi; omega⟩).val
  simp only [block_snake_reverse_crossout_nel_ef1_A, block_snake_reverse_crossout_nel_ef1_B]
  rw [dif_neg (by simp : ¬ (⟨i.val+2,
    by have h := block_snake_reverse_crossout_nel_ef1_ltLast k hk i hi; omega⟩ : Fin (k+1)).val = 0)]
  simp
  omega

theorem block_snake_reverse_crossout_nel_ef1_NEL (k : ℕ) (hk : 0 < k)
    (u : Fin 2 → Fin (2*k+1) → ℝ) (π : Fin (2*k+1) → Fin (2*k+1))
    (hinj : Function.Injective π)
    (hmin : ∀ t j : Fin (2*k+1), t < j →
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π t) ≤
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π j))
    (y : Fin (2*k+1))
    (hy : y ∈ picking_reverse_crossout_allocation (block_snake_seq_two k) π 1) :
    ∃ f : Fin (2*k+1) → Fin (2*k+1),
      (∀ z ∈ (picking_reverse_crossout_allocation (block_snake_seq_two k) π 1).erase y,
        f z ∈ picking_reverse_crossout_allocation (block_snake_seq_two k) π 0) ∧
      (∀ z1 ∈ (picking_reverse_crossout_allocation (block_snake_seq_two k) π 1).erase y,
       ∀ z2 ∈ (picking_reverse_crossout_allocation (block_snake_seq_two k) π 1).erase y,
        f z1 = f z2 → z1 = z2) ∧
      ∀ z ∈ (picking_reverse_crossout_allocation (block_snake_seq_two k) π 1).erase y,
        u 0 z ≤ u 0 (f z) := by
  rw [block_snake_reverse_crossout_nel_ef1_allocOne] at hy
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨m, hm⟩ := hy
  have hyex : ∃ j : Fin (k+1), π (block_snake_reverse_crossout_nel_ef1_B k j) = y := ⟨m, hm⟩
  have hJm : π (block_snake_reverse_crossout_nel_ef1_B k
      (block_snake_reverse_crossout_nel_ef1_J k π y)) = y :=
    block_snake_reverse_crossout_nel_ef1_J_spec k π y hyex
  refine ⟨block_snake_reverse_crossout_nel_ef1_F0 k hk π y, ?_, ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_erase] at hz
    obtain ⟨-, hzA⟩ := hz
    rw [block_snake_reverse_crossout_nel_ef1_allocOne] at hzA
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hzA
    obtain ⟨i, hi⟩ := hzA
    have hJ : block_snake_reverse_crossout_nel_ef1_J k π z = i := by
      rw [← hi]; exact block_snake_reverse_crossout_nel_ef1_J_apply k π hinj i
    rw [block_snake_reverse_crossout_nel_ef1_F0, hJ,
      block_snake_reverse_crossout_nel_ef1_allocZero]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨block_snake_reverse_crossout_nel_ef1_T k hk
      (block_snake_reverse_crossout_nel_ef1_J k π y) i, rfl⟩
  · intro z1 hz1 z2 hz2 he
    rw [Finset.mem_erase] at hz1 hz2
    obtain ⟨hz1y, hz1A⟩ := hz1
    obtain ⟨hz2y, hz2A⟩ := hz2
    rw [block_snake_reverse_crossout_nel_ef1_allocOne] at hz1A hz2A
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz1A hz2A
    obtain ⟨i1, hi1⟩ := hz1A
    obtain ⟨i2, hi2⟩ := hz2A
    have hJ1 : block_snake_reverse_crossout_nel_ef1_J k π z1 = i1 := by
      rw [← hi1]; exact block_snake_reverse_crossout_nel_ef1_J_apply k π hinj i1
    have hJ2 : block_snake_reverse_crossout_nel_ef1_J k π z2 = i2 := by
      rw [← hi2]; exact block_snake_reverse_crossout_nel_ef1_J_apply k π hinj i2
    rw [block_snake_reverse_crossout_nel_ef1_F0, block_snake_reverse_crossout_nel_ef1_F0,
      hJ1, hJ2] at he
    have hi1m : i1 ≠ block_snake_reverse_crossout_nel_ef1_J k π y := by
      intro h; apply hz1y; rw [← hi1, h, hJm]
    have hi2m : i2 ≠ block_snake_reverse_crossout_nel_ef1_J k π y := by
      intro h; apply hz2y; rw [← hi2, h, hJm]
    have hb : block_snake_reverse_crossout_nel_ef1_T k hk
        (block_snake_reverse_crossout_nel_ef1_J k π y) i1 =
        block_snake_reverse_crossout_nel_ef1_T k hk
          (block_snake_reverse_crossout_nel_ef1_J k π y) i2 :=
      hinj.comp (block_snake_reverse_crossout_nel_ef1_A_inj k) he
    have hie : i1 = i2 := block_snake_reverse_crossout_nel_ef1_T_inj k hk
      (block_snake_reverse_crossout_nel_ef1_J k π y) hi1m hi2m hb
    rw [← hi1, ← hi2, hie]
  · intro z hz
    rw [Finset.mem_erase] at hz
    obtain ⟨hzy, hzA⟩ := hz
    rw [block_snake_reverse_crossout_nel_ef1_allocOne] at hzA
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hzA
    obtain ⟨i, hi⟩ := hzA
    have hJ : block_snake_reverse_crossout_nel_ef1_J k π z = i := by
      rw [← hi]; exact block_snake_reverse_crossout_nel_ef1_J_apply k π hinj i
    have him : i ≠ block_snake_reverse_crossout_nel_ef1_J k π y := by
      intro h; apply hzy; rw [← hi, h, hJm]
    have hJ' : block_snake_reverse_crossout_nel_ef1_J k π
        (π (block_snake_reverse_crossout_nel_ef1_B k i)) = i :=
      block_snake_reverse_crossout_nel_ef1_J_apply k π hinj i
    rw [show z = π (block_snake_reverse_crossout_nel_ef1_B k i) from hi.symm,
      block_snake_reverse_crossout_nel_ef1_F0, hJ']
    exact block_snake_reverse_crossout_nel_ef1_U0 k hk u π hmin
      (block_snake_reverse_crossout_nel_ef1_J k π y) i him

theorem block_snake_reverse_crossout_nel_ef1_EF1Back (k : ℕ) (hk : 0 < k)
    (u : Fin 2 → Fin (2*k+1) → ℝ) (π : Fin (2*k+1) → Fin (2*k+1))
    (hinj : Function.Injective π)
    (hmin : ∀ t j : Fin (2*k+1), t < j →
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π t) ≤
      u (if (block_snake_seq_two k).reverse.getD t.val 0 = 0 then 1 else 0) (π j)) :
    ∃ y ∈ picking_reverse_crossout_allocation (block_snake_seq_two k) π 0,
      ∃ f : Fin (2*k+1) → Fin (2*k+1),
        (∀ z ∈ (picking_reverse_crossout_allocation (block_snake_seq_two k) π 0).erase y,
          f z ∈ picking_reverse_crossout_allocation (block_snake_seq_two k) π 1) ∧
        (∀ z1 ∈ (picking_reverse_crossout_allocation (block_snake_seq_two k) π 0).erase y,
         ∀ z2 ∈ (picking_reverse_crossout_allocation (block_snake_seq_two k) π 0).erase y,
          f z1 = f z2 → z1 = z2) ∧
        ∀ z ∈ (picking_reverse_crossout_allocation (block_snake_seq_two k) π 0).erase y,
          u 1 z ≤ u 1 (f z) := by
  refine ⟨π (block_snake_reverse_crossout_nel_ef1_A k
    (block_snake_reverse_crossout_nel_ef1_last k hk)), ?_,
    block_snake_reverse_crossout_nel_ef1_F1 k hk π, ?_, ?_, ?_⟩
  · rw [block_snake_reverse_crossout_nel_ef1_allocZero]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨block_snake_reverse_crossout_nel_ef1_last k hk, rfl⟩
  · intro z hz
    rw [Finset.mem_erase] at hz
    obtain ⟨-, hzA⟩ := hz
    rw [block_snake_reverse_crossout_nel_ef1_allocZero] at hzA
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hzA
    obtain ⟨i, hi⟩ := hzA
    have hI : block_snake_reverse_crossout_nel_ef1_I k
        (block_snake_reverse_crossout_nel_ef1_last k hk) π z = i := by
      rw [← hi]
      exact block_snake_reverse_crossout_nel_ef1_I_apply k
        (block_snake_reverse_crossout_nel_ef1_last k hk) π hinj i
    rw [block_snake_reverse_crossout_nel_ef1_F1, hI,
      block_snake_reverse_crossout_nel_ef1_allocOne]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨block_snake_reverse_crossout_nel_ef1_T2 k hk i, rfl⟩
  · intro z1 hz1 z2 hz2 he
    rw [Finset.mem_erase] at hz1 hz2
    obtain ⟨hz1y, hz1A⟩ := hz1
    obtain ⟨hz2y, hz2A⟩ := hz2
    rw [block_snake_reverse_crossout_nel_ef1_allocZero] at hz1A hz2A
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz1A hz2A
    obtain ⟨i1, hi1⟩ := hz1A
    obtain ⟨i2, hi2⟩ := hz2A
    have hI1 : block_snake_reverse_crossout_nel_ef1_I k
        (block_snake_reverse_crossout_nel_ef1_last k hk) π z1 = i1 := by
      rw [← hi1]
      exact block_snake_reverse_crossout_nel_ef1_I_apply k
        (block_snake_reverse_crossout_nel_ef1_last k hk) π hinj i1
    have hI2 : block_snake_reverse_crossout_nel_ef1_I k
        (block_snake_reverse_crossout_nel_ef1_last k hk) π z2 = i2 := by
      rw [← hi2]
      exact block_snake_reverse_crossout_nel_ef1_I_apply k
        (block_snake_reverse_crossout_nel_ef1_last k hk) π hinj i2
    rw [block_snake_reverse_crossout_nel_ef1_F1, block_snake_reverse_crossout_nel_ef1_F1,
      hI1, hI2] at he
    have hi1m : i1 ≠ block_snake_reverse_crossout_nel_ef1_last k hk := by
      intro h; apply hz1y; rw [← hi1, h]
    have hi2m : i2 ≠ block_snake_reverse_crossout_nel_ef1_last k hk := by
      intro h; apply hz2y; rw [← hi2, h]
    have hb : block_snake_reverse_crossout_nel_ef1_T2 k hk i1 =
        block_snake_reverse_crossout_nel_ef1_T2 k hk i2 :=
      hinj.comp (block_snake_reverse_crossout_nel_ef1_B_inj k) he
    have hie : i1 = i2 := block_snake_reverse_crossout_nel_ef1_T2_inj k hk hi1m hi2m hb
    rw [← hi1, ← hi2, hie]
  · intro z hz
    rw [Finset.mem_erase] at hz
    obtain ⟨hzy, hzA⟩ := hz
    rw [block_snake_reverse_crossout_nel_ef1_allocZero] at hzA
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hzA
    obtain ⟨i, hi⟩ := hzA
    have hI : block_snake_reverse_crossout_nel_ef1_I k
        (block_snake_reverse_crossout_nel_ef1_last k hk) π z = i := by
      rw [← hi]
      exact block_snake_reverse_crossout_nel_ef1_I_apply k
        (block_snake_reverse_crossout_nel_ef1_last k hk) π hinj i
    have him : i ≠ block_snake_reverse_crossout_nel_ef1_last k hk := by
      intro h; apply hzy; rw [← hi, h]
    have hI' : block_snake_reverse_crossout_nel_ef1_I k
        (block_snake_reverse_crossout_nel_ef1_last k hk) π
        (π (block_snake_reverse_crossout_nel_ef1_A k i)) = i :=
      block_snake_reverse_crossout_nel_ef1_I_apply k
        (block_snake_reverse_crossout_nel_ef1_last k hk) π hinj i
    rw [show z = π (block_snake_reverse_crossout_nel_ef1_A k i) from hi.symm,
      block_snake_reverse_crossout_nel_ef1_F1, hI']
    exact block_snake_reverse_crossout_nel_ef1_U1 k hk u π hmin i him

theorem block_snake_reverse_crossout_nel_ef1 (k : ℕ) (u : Fin 2 → Fin (2*k+1) → ℝ) (π : Fin (2*k+1) → Fin (2*k+1))
  (hπ : picking_reverse_crossout_valid u (block_snake_seq_two k) π) :
  is_nel_pd (fun i x y => u i x ≤ u i y) (picking_reverse_crossout_allocation (block_snake_seq_two k) π) ∧
  is_ef1_pd (fun i x y => u i x ≤ u i y) (picking_reverse_crossout_allocation (block_snake_seq_two k) π) := by
  rw [picking_reverse_crossout_valid] at hπ
  obtain ⟨-, hinj, hmin⟩ := hπ
  set A := picking_reverse_crossout_allocation (block_snake_seq_two k) π with hA
  have hc0 : (A 0).card = k := by rw [hA]; exact block_snake_reverse_crossout_nel_ef1_cardZero k π hinj.1
  have hc1 : (A 1).card = k + 1 := by rw [hA]; exact block_snake_reverse_crossout_nel_ef1_cardOne k π hinj.1
  have hcase : ∀ i j : Fin 2, (A i).card < (A j).card → i = 0 ∧ j = 1 := by
    intro i j hij
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact absurd hij (lt_irrefl _)
    · exact ⟨rfl, rfl⟩
    · omega
    · exact absurd hij (lt_irrefl _)
  refine ⟨?_, ?_⟩
  · intro i j hij y hy
    obtain ⟨rfl, rfl⟩ := hcase i j hij
    by_cases hk : k = 0
    · subst hk
      have hy1 : (A 1).erase y = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [Finset.card_erase_of_mem hy]; simp [hc1]
      exact ⟨fun z => z,
        (fun z hz => absurd (by rwa [hy1] at hz) (Finset.notMem_empty z)),
        (fun z1 hz1 => absurd (by rwa [hy1] at hz1) (Finset.notMem_empty z1)),
        (fun z hz => absurd (by rwa [hy1] at hz) (Finset.notMem_empty z))⟩
    · exact block_snake_reverse_crossout_nel_ef1_NEL k (Nat.pos_of_ne_zero hk) u π hinj.1 hmin y hy
  · intro i j
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · left
      exact ⟨fun z => z, (fun z hz => hz), (fun z1 _ z2 _ h => h), (fun z _ => le_refl _)⟩
    · by_cases hk : k = 0
      · subst hk
        right
        have hne : (A 1).Nonempty := by rw [← Finset.card_pos, hc1]; omega
        obtain ⟨y, hy⟩ := hne
        have hy1 : (A 1).erase y = ∅ := by
          apply Finset.card_eq_zero.mp
          rw [Finset.card_erase_of_mem hy]; simp [hc1]
        exact ⟨y, hy, fun z => z,
          (fun z hz => absurd (by rwa [hy1] at hz) (Finset.notMem_empty z)),
          (fun z1 hz1 => absurd (by rwa [hy1] at hz1) (Finset.notMem_empty z1)),
          (fun z hz => absurd (by rwa [hy1] at hz) (Finset.notMem_empty z))⟩
      · right
        have hne : (A 1).Nonempty := by rw [← Finset.card_pos, hc1]; omega
        obtain ⟨y, hy⟩ := hne
        exact ⟨y, hy, block_snake_reverse_crossout_nel_ef1_NEL k (Nat.pos_of_ne_zero hk) u π hinj.1 hmin y hy⟩
    · by_cases hk : k = 0
      · subst hk
        left
        have hA0 : A 0 = ∅ := Finset.card_eq_zero.mp hc0
        exact ⟨fun z => z,
          (fun z hz => absurd (by rwa [hA0] at hz) (Finset.notMem_empty z)),
          (fun z1 hz1 => absurd (by rwa [hA0] at hz1) (Finset.notMem_empty z1)),
          (fun z hz => absurd (by rwa [hA0] at hz) (Finset.notMem_empty z))⟩
      · exact Or.inr (block_snake_reverse_crossout_nel_ef1_EF1Back k (Nat.pos_of_ne_zero hk) u π hinj.1 hmin)
    · left
      exact ⟨fun z => z, (fun z hz => hz), (fun z1 _ z2 _ h => h), (fun z _ => le_refl _)⟩
