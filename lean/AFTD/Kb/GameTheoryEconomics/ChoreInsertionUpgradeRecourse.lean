import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChoreInsertionAllocation
import AFTD.Kb.GameTheoryEconomics.HasUpgradeRecourse
import AFTD.Kb.GameTheoryEconomics.ChoreInsertionSlots
import AFTD.Kb.GameTheoryEconomics.ChoreInsertPass
import AFTD.Kb.GameTheoryEconomics.IsUpgradeFeasible

/-!
# chore_insertion_upgrade_recourse

Topic: fair_division   Node: 8c3a81bf9705

Provenance: helper lemma. arXiv:2611.00432, Lemma 3.1

For any number of agents n : ℕ, picking sequence σ : ℕ → Fin n, and chore costs c : Fin n → ℕ → ℝ, chore insertion satisfies upgrade recourse: has_upgrade_recourse n c (chore_insertion_allocation σ c).
-/

open Finset

theorem chore_insertion_upgrade_recourse_pass_ge {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (k : ℕ) (slots : ℕ → ℕ) (b : ℕ) (j : ℕ) (hj : k ≤ j) :
    (chore_insert_pass σ c k slots b).1 j = slots j := by
  induction k generalizing slots b with
  | zero => rfl
  | succ k ih =>
    rw [chore_insert_pass]
    dsimp only
    split
    · simp only
      rw [Function.update_apply]
      split_ifs with h
      · subst h; omega
      · exact ih slots b (by omega)
    · exact ih slots b (by omega)

theorem chore_insertion_upgrade_recourse_pass_lt {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (k : ℕ) (slots : ℕ → ℕ) (b : ℕ) (j : ℕ) (hj : j < k) :
    (chore_insert_pass σ c (k + 1) slots b).1 j = (chore_insert_pass σ c k slots b).1 j := by
  rw [chore_insert_pass]
  dsimp only
  split
  · simp only
    rw [Function.update_apply]
    split_ifs with h
    · omega
    · rfl
  · rfl

theorem chore_insertion_upgrade_recourse_pass_lt_m {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (j m : ℕ) (slots : ℕ → ℕ) (b : ℕ) (hj : j < m) :
    (chore_insert_pass σ c m slots b).1 j = (chore_insert_pass σ c (j + 1) slots b).1 j := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : j < m
    · rw [chore_insertion_upgrade_recourse_pass_lt σ c m slots b j h]
      exact ih h
    · have : m = j := by omega
      subst this
      rfl

theorem chore_insertion_upgrade_recourse_pass_cost_le {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (j : ℕ) (slots : ℕ → ℕ) (b : ℕ) :
    c (σ j) ((chore_insert_pass σ c (j + 1) slots b).1 j) ≤ c (σ j) (slots j) := by
  rw [chore_insert_pass]
  dsimp only
  rw [chore_insertion_upgrade_recourse_pass_ge σ c j slots b j (by omega)]
  split
  · rename_i h
    simp only
    rw [Function.update_self]
    cases h with
    | inl h1 => linarith
    | inr h2 => linarith
  · simp only
    rw [chore_insertion_upgrade_recourse_pass_ge σ c j slots b j (by omega)]

theorem chore_insertion_upgrade_recourse_pass_cost_le_m {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (j m : ℕ) (slots : ℕ → ℕ) (b : ℕ) (hj : j < m) :
    c (σ j) ((chore_insert_pass σ c m slots b).1 j) ≤ c (σ j) (slots j) := by
  rw [chore_insertion_upgrade_recourse_pass_lt_m σ c j m slots b hj]
  exact chore_insertion_upgrade_recourse_pass_cost_le σ c j slots b

theorem chore_insertion_upgrade_recourse_pass_image {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (k : ℕ) (slots : ℕ → ℕ) (b : ℕ) :
    Finset.image (chore_insert_pass σ c k slots b).1 (Finset.range k) ∪ {(chore_insert_pass σ c k slots b).2} =
    Finset.image slots (Finset.range k) ∪ {b} := by
  induction k generalizing slots b with
  | zero =>
    rw [chore_insert_pass]
  | succ k ih =>
    rw [chore_insert_pass]
    dsimp only
    set res := chore_insert_pass σ c k slots b
    have h_ih := ih slots b
    have h_ge : res.1 k = slots k := chore_insertion_upgrade_recourse_pass_ge σ c k slots b k (le_refl k)
    rw [range_add_one, image_insert, insert_union]
    split
    · rename_i h
      dsimp only
      rw [Function.update_self]
      have h_eq : Finset.image (Function.update res.1 k res.2) (range k) = Finset.image res.1 (range k) := by
        apply Finset.image_congr
        intro x hx
        have : x < k := mem_range.mp (mem_coe.mp hx)
        rw [Function.update_of_ne (by omega)]
      rw [h_eq]
      have h1 : insert res.2 (image res.1 (range k) ∪ {res.1 k}) =
                insert (res.1 k) (image res.1 (range k) ∪ {res.2}) := by
        ext x; simp only [mem_insert, mem_union, mem_singleton]; tauto
      rw [h1, h_ge]
      have h2 : insert (slots k) (image res.1 (range k) ∪ {res.2}) =
                insert (slots k) (image slots (range k) ∪ {b}) := by rw [h_ih]
      rw [h2]
      ext x
      simp only [mem_insert, mem_union, mem_singleton, image_insert]
      tauto
    · rename_i h
      dsimp only
      rw [h_ge]
      have h2 : insert (slots k) (image res.1 (range k) ∪ {res.2}) =
                insert (slots k) (image slots (range k) ∪ {b}) := by rw [h_ih]
      rw [h2]
      ext x
      simp only [mem_insert, mem_union, mem_singleton, image_insert]
      tauto

theorem chore_insertion_upgrade_recourse_slots_image {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (m : ℕ) :
    Finset.image (chore_insertion_slots σ c m) (Finset.range m) = Finset.range m := by
  induction m with
  | zero =>
    rw [chore_insertion_slots]
    simp only [range_zero, image_empty]
  | succ m ih =>
    rw [chore_insertion_slots]
    dsimp only
    set prev := chore_insertion_slots σ c m
    set pass := chore_insert_pass σ c m prev m
    rw [range_add_one, image_insert]
    rw [Function.update_self]
    have h_eq : Finset.image (Function.update pass.1 m pass.2) (range m) = Finset.image pass.1 (range m) := by
      apply Finset.image_congr
      intro x hx
      have : x < m := mem_range.mp (mem_coe.mp hx)
      rw [Function.update_of_ne (by omega)]
    rw [h_eq]
    have h_union : insert pass.2 (image pass.1 (range m)) = image pass.1 (range m) ∪ {pass.2} := by
      ext x; simp only [mem_insert, mem_union, mem_singleton]; tauto
    rw [h_union, chore_insertion_upgrade_recourse_pass_image σ c m prev m, ih]
    rw [union_comm, ← insert_eq]

theorem chore_insertion_upgrade_recourse_slots_lt {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (m k : ℕ) (hk : k < m) :
    chore_insertion_slots σ c m k < m := by
  have : chore_insertion_slots σ c m k ∈ Finset.image (chore_insertion_slots σ c m) (Finset.range m) := by
    rw [mem_image]
    exact ⟨k, mem_range.mpr hk, rfl⟩
  rw [chore_insertion_upgrade_recourse_slots_image, mem_range] at this
  exact this

theorem chore_insertion_upgrade_recourse_slots_injOn {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (m : ℕ) :
    Set.InjOn (chore_insertion_slots σ c m) (Finset.range m : Set ℕ) := by
  apply injOn_of_card_image_eq
  rw [chore_insertion_upgrade_recourse_slots_image]

theorem chore_insertion_upgrade_recourse_slots_surj {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (m d : ℕ) (hd : d < m) :
    ∃ k < m, chore_insertion_slots σ c m k = d := by
  have hd' : d ∈ Finset.range m := mem_range.mpr hd
  rw [← chore_insertion_upgrade_recourse_slots_image σ c m] at hd'
  rcases mem_image.mp hd' with ⟨k, hk, rfl⟩
  exact ⟨k, mem_range.mp hk, rfl⟩

theorem chore_insertion_upgrade_recourse_slots_cost_le {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (m k : ℕ) (hk : k < m) :
    c (σ k) (chore_insertion_slots σ c (m + 1) k) ≤ c (σ k) (chore_insertion_slots σ c m k) := by
  have h_succ : chore_insertion_slots σ c (m + 1) k = (chore_insert_pass σ c m (chore_insertion_slots σ c m) m).1 k := by
    rw [chore_insertion_slots]
    dsimp only
    rw [Function.update_apply]
    split_ifs with h
    · omega
    · rfl
  rw [h_succ]
  exact chore_insertion_upgrade_recourse_pass_cost_le_m σ c k m (chore_insertion_slots σ c m) m hk

theorem chore_insertion_upgrade_recourse_allocation_eq {n : ℕ} (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) (m : ℕ)
    (k : ℕ) (hk : k < m) :
    chore_insertion_allocation σ c m ⟨chore_insertion_slots σ c m k, chore_insertion_upgrade_recourse_slots_lt σ c m k hk⟩ = σ k := by
  unfold chore_insertion_allocation
  dsimp only
  have h : ∃ k' < m, chore_insertion_slots σ c m k' = chore_insertion_slots σ c m k := ⟨k, hk, rfl⟩
  rw [dif_pos h]
  have h_choose := Classical.choose_spec h
  have h1 : Classical.choose h ∈ (range m : Set ℕ) := mem_range.mpr h_choose.1
  have h2 : k ∈ (range m : Set ℕ) := mem_range.mpr hk
  have := chore_insertion_upgrade_recourse_slots_injOn σ c m h1 h2 h_choose.2
  rw [this]

/-- Chore insertion satisfies upgrade recourse at every arrival. -/
theorem chore_insertion_upgrade_recourse (n : ℕ) (σ : ℕ → Fin n) (c : Fin n → ℕ → ℝ) : has_upgrade_recourse n c (chore_insertion_allocation σ c) := by
  intro m
  unfold is_upgrade_feasible
  intro i
  let slot_of (d : {d : Fin m // chore_insertion_allocation σ c m d = i}) : ℕ :=
    Classical.choose (chore_insertion_upgrade_recourse_slots_surj σ c m d.val.val d.val.isLt)
  have h_slot (d : {d : Fin m // chore_insertion_allocation σ c m d = i}) :
      slot_of d < m ∧ chore_insertion_slots σ c m (slot_of d) = d.val.val :=
    Classical.choose_spec (chore_insertion_upgrade_recourse_slots_surj σ c m d.val.val d.val.isLt)
  have h_owner (d : {d : Fin m // chore_insertion_allocation σ c m d = i}) : σ (slot_of d) = i := by
    have hd_prop := d.prop
    unfold chore_insertion_allocation at hd_prop
    have h : ∃ k < m, chore_insertion_slots σ c m k = d.val.val := ⟨slot_of d, (h_slot d).1, (h_slot d).2⟩
    rw [dif_pos h] at hd_prop
    have h_ch := Classical.choose_spec h
    have h1 : Classical.choose h ∈ (range m : Set ℕ) := mem_range.mpr h_ch.1
    have h2 : slot_of d ∈ (range m : Set ℕ) := mem_range.mpr (h_slot d).1
    have h_eq : Classical.choose h = slot_of d :=
      chore_insertion_upgrade_recourse_slots_injOn σ c m h1 h2 (h_ch.2.trans (h_slot d).2.symm)
    rwa [h_eq] at hd_prop
  have h_slot_lt_succ (d : {d : Fin m // chore_insertion_allocation σ c m d = i}) : slot_of d < m + 1 := by
    have := (h_slot d).1; omega
  let φ (d : {d : Fin m // chore_insertion_allocation σ c m d = i}) :
      {d' : Fin (m + 1) // chore_insertion_allocation σ c (m + 1) d' = i} :=
    ⟨⟨chore_insertion_slots σ c (m + 1) (slot_of d),
      chore_insertion_upgrade_recourse_slots_lt σ c (m + 1) (slot_of d) (h_slot_lt_succ d)⟩, by
      have := chore_insertion_upgrade_recourse_allocation_eq σ c (m + 1) (slot_of d) (h_slot_lt_succ d)
      rw [this, h_owner d]⟩
  refine ⟨φ, ?_, ?_⟩
  · intro d1 d2 h_eq
    apply Subtype.ext
    apply Fin.ext
    injection h_eq with h_val
    injection h_val with h_slot_eq
    have hk1 : slot_of d1 ∈ (range (m + 1) : Set ℕ) := mem_range.mpr (h_slot_lt_succ d1)
    have hk2 : slot_of d2 ∈ (range (m + 1) : Set ℕ) := mem_range.mpr (h_slot_lt_succ d2)
    have h_slot_same : slot_of d1 = slot_of d2 :=
      chore_insertion_upgrade_recourse_slots_injOn σ c (m + 1) hk1 hk2 h_slot_eq
    have hd1 := (h_slot d1).2
    have hd2 := (h_slot d2).2
    rw [h_slot_same] at hd1
    exact hd1.symm.trans hd2
  · intro d
    dsimp only [φ]
    have h_cost := chore_insertion_upgrade_recourse_slots_cost_le σ c m (slot_of d) (h_slot d).1
    rw [h_owner d] at h_cost
    rw [(h_slot d).2] at h_cost
    exact h_cost
