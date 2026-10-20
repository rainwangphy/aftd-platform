import AFTD.Prelude
import AFTD.Kb.Tcs.NfaRunCountList

/-!
# nfa_run_penultimate_fiber

Topic: automata   Node: 6f5f175fe9f6

Provenance: helper lemma. step towards nfa_run_count_list_concat

The number of runs of w ++ [a] from p to q with penultimate state s equals the number of runs of w from p to s if q ∈ M.step s a, and 0 otherwise.
-/

def nfa_run_penultimate_fiber_to_r0 {α σ : Type*} (w : List α) (a : α)
    (r : Fin ((w ++ [a]).length + 1) → σ) : Fin (w.length + 1) → σ :=
  fun j => r ⟨j.val, by
    have hj := j.isLt
    simp only [List.length_append, List.length_singleton] at *
    omega⟩

def nfa_run_penultimate_fiber_from_r0 {α σ : Type*} (w : List α) (a : α) (q : σ)
    (r0 : Fin (w.length + 1) → σ) : Fin ((w ++ [a]).length + 1) → σ :=
  fun k => if h : k.val ≤ w.length then r0 ⟨k.val, Nat.lt_succ_of_le h⟩ else q

lemma nfa_run_penultimate_fiber_from_r0_of_le {α σ : Type*} (w : List α) (a : α) (q : σ)
    (r0 : Fin (w.length + 1) → σ) (k : Fin ((w ++ [a]).length + 1)) (h : k.val ≤ w.length) :
    nfa_run_penultimate_fiber_from_r0 w a q r0 k = r0 ⟨k.val, Nat.lt_succ_of_le h⟩ := by
  change (if h' : k.val ≤ w.length then _ else _) = _
  rw [dif_pos h]

lemma nfa_run_penultimate_fiber_from_r0_of_gt {α σ : Type*} (w : List α) (a : α) (q : σ)
    (r0 : Fin (w.length + 1) → σ) (k : Fin ((w ++ [a]).length + 1)) (h : ¬ k.val ≤ w.length) :
    nfa_run_penultimate_fiber_from_r0 w a q r0 k = q := by
  change (if h' : k.val ≤ w.length then _ else _) = _
  rw [dif_neg h]

lemma nfa_run_penultimate_fiber_to_from_r0 {α σ : Type*} (w : List α) (a : α) (q : σ)
    (r0 : Fin (w.length + 1) → σ) :
    nfa_run_penultimate_fiber_to_r0 w a (nfa_run_penultimate_fiber_from_r0 w a q r0) = r0 := by
  ext ⟨j, hj⟩
  dsimp [nfa_run_penultimate_fiber_to_r0, nfa_run_penultimate_fiber_from_r0]
  have hle : j ≤ w.length := Nat.le_of_lt_succ hj
  rw [dif_pos hle]

lemma nfa_run_penultimate_fiber_from_to_r0 {α σ : Type*} (w : List α) (a : α) (q : σ)
    (r : Fin ((w ++ [a]).length + 1) → σ)
    (hq : r (Fin.last (w ++ [a]).length) = q) :
    nfa_run_penultimate_fiber_from_r0 w a q (nfa_run_penultimate_fiber_to_r0 w a r) = r := by
  ext ⟨k, hk⟩
  dsimp [nfa_run_penultimate_fiber_to_r0, nfa_run_penultimate_fiber_from_r0]
  split_ifs with h
  · rfl
  · have hlen : (w ++ [a]).length = w.length + 1 := by simp
    have hk_eq : k = (w ++ [a]).length := by
      rw [hlen] at hk ⊢
      omega
    have : (⟨k, hk⟩ : Fin ((w ++ [a]).length + 1)) = Fin.last (w ++ [a]).length := by
      ext; exact hk_eq
    rw [this, hq]

lemma nfa_run_penultimate_fiber_get_append_left_elem {α : Type*} (w : List α) (a : α) (i : Fin w.length)
    (h : i.val < (w ++ [a]).length) :
    (w ++ [a]).get ⟨i.val, h⟩ = w.get i := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact List.getElem_append_left i.isLt

lemma nfa_run_penultimate_fiber_get_append_last_elem {α : Type*} (w : List α) (a : α)
    (h : w.length < (w ++ [a]).length) :
    (w ++ [a]).get ⟨w.length, h⟩ = a := by
  rw [List.get_eq_getElem]
  have hright := List.getElem_append_right (le_refl w.length) (h₂ := h)
  rw [hright]
  simp

lemma nfa_run_penultimate_fiber_to_r0_mem {α σ : Type*} (M : NFA α σ) (w : List α) (a : α) (p s : σ)
    {r : Fin ((w ++ [a]).length + 1) → σ}
    (hr0 : r 0 = p)
    (hr_step : ∀ i : Fin (w ++ [a]).length, r i.succ ∈ M.step (r i.castSucc) ((w ++ [a]).get i))
    (hr_pen : r ⟨w.length, by simp⟩ = s) :
    (nfa_run_penultimate_fiber_to_r0 w a r) 0 = p ∧
    (nfa_run_penultimate_fiber_to_r0 w a r) (Fin.last w.length) = s ∧
    ∀ i : Fin w.length, (nfa_run_penultimate_fiber_to_r0 w a r) i.succ ∈ M.step ((nfa_run_penultimate_fiber_to_r0 w a r) i.castSucc) (w.get i) := by
  refine ⟨?_, ?_, ?_⟩
  · show r ⟨(0 : Fin (w.length + 1)).val, _⟩ = p
    have : (⟨(0 : Fin (w.length + 1)).val, by simp⟩ : Fin ((w ++ [a]).length + 1)) = 0 := by
      ext; rfl
    rw [this, hr0]
  · show r ⟨(Fin.last w.length).val, _⟩ = s
    have : (⟨(Fin.last w.length).val, by simp⟩ : Fin ((w ++ [a]).length + 1)) = ⟨w.length, by simp⟩ := by
      ext; rfl
    rw [this, hr_pen]
  · intro i
    have h1 : i.val < (w ++ [a]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hstep := hr_step ⟨i.val, h1⟩
    have hcast : (⟨i.val, h1⟩ : Fin (List.length (w ++ [a]))).castSucc =
      (⟨(i.castSucc).val, by simp; omega⟩ : Fin ((w ++ [a]).length + 1)) := by
      ext; rfl
    have hsucc : (⟨i.val, h1⟩ : Fin (List.length (w ++ [a]))).succ =
      (⟨(i.succ).val, by simp⟩ : Fin ((w ++ [a]).length + 1)) := by
      ext; rfl
    have hget := nfa_run_penultimate_fiber_get_append_left_elem w a i h1
    rw [hcast, hsucc, hget] at hstep
    exact hstep

lemma nfa_run_penultimate_fiber_to_r0_step_last {α σ : Type*} (M : NFA α σ) (w : List α) (a : α) (q s : σ)
    {r : Fin ((w ++ [a]).length + 1) → σ}
    (hr_last : r (Fin.last (w ++ [a]).length) = q)
    (hr_step : ∀ i : Fin (w ++ [a]).length, r i.succ ∈ M.step (r i.castSucc) ((w ++ [a]).get i))
    (hr_pen : r ⟨w.length, by simp⟩ = s) :
    q ∈ M.step s a := by
  have hlen : w.length < (w ++ [a]).length := by
    simp only [List.length_append, List.length_singleton]; omega
  have hstep := hr_step ⟨w.length, hlen⟩
  have hcast : (⟨w.length, hlen⟩ : Fin (w ++ [a]).length).castSucc = ⟨w.length, by simp⟩ := by
    ext; rfl
  have hsucc : (⟨w.length, hlen⟩ : Fin (w ++ [a]).length).succ = Fin.last (w ++ [a]).length := by
    ext; simp
  have hget := nfa_run_penultimate_fiber_get_append_last_elem w a hlen
  rw [hcast, hsucc, hget, hr_pen, hr_last] at hstep
  exact hstep

lemma nfa_run_penultimate_fiber_from_r0_mem {α σ : Type*} (M : NFA α σ) (w : List α) (a : α) (p q s : σ)
    {r0 : Fin (w.length + 1) → σ}
    (hr0_0 : r0 0 = p)
    (hr0_last : r0 (Fin.last w.length) = s)
    (hr0_step : ∀ i : Fin w.length, r0 i.succ ∈ M.step (r0 i.castSucc) (w.get i))
    (hq : q ∈ M.step s a) :
    (nfa_run_penultimate_fiber_from_r0 w a q r0) 0 = p ∧
    (nfa_run_penultimate_fiber_from_r0 w a q r0) (Fin.last (w ++ [a]).length) = q ∧
    (∀ i : Fin (w ++ [a]).length, (nfa_run_penultimate_fiber_from_r0 w a q r0) i.succ ∈ M.step ((nfa_run_penultimate_fiber_from_r0 w a q r0) i.castSucc) ((w ++ [a]).get i)) ∧
    (nfa_run_penultimate_fiber_from_r0 w a q r0) ⟨w.length, by simp⟩ = s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nfa_run_penultimate_fiber_from_r0_of_le w a q r0 0 (Nat.zero_le _)]
    have : (⟨(0 : Fin ((w ++ [a]).length + 1)).val, Nat.lt_succ_of_le (Nat.zero_le _)⟩ : Fin (w.length + 1)) = 0 := by
      ext; rfl
    rw [this, hr0_0]
  · have hlen : (w ++ [a]).length = w.length + 1 := by simp
    have hgt : ¬ (Fin.last (w ++ [a]).length).val ≤ w.length := by
      rw [Fin.val_last, hlen]
      omega
    exact nfa_run_penultimate_fiber_from_r0_of_gt w a q r0 _ hgt
  · intro i
    by_cases hi : i.val < w.length
    · let j : Fin w.length := ⟨i.val, hi⟩
      have hj_step := hr0_step j
      have hcast_le : i.castSucc.val ≤ w.length := by
        have : i.castSucc.val = i.val := rfl
        omega
      have hsucc_le : i.succ.val ≤ w.length := by
        have : i.succ.val = i.val + 1 := rfl
        omega
      rw [nfa_run_penultimate_fiber_from_r0_of_le w a q r0 _ hcast_le, nfa_run_penultimate_fiber_from_r0_of_le w a q r0 _ hsucc_le]
      have hj_cast : (⟨i.castSucc.val, Nat.lt_succ_of_le hcast_le⟩ : Fin (w.length + 1)) = j.castSucc := by
        ext; rfl
      have hj_succ : (⟨i.succ.val, Nat.lt_succ_of_le hsucc_le⟩ : Fin (w.length + 1)) = j.succ := by
        ext; rfl
      rw [hj_cast, hj_succ]
      have h1 : i.val < (w ++ [a]).length := i.isLt
      have heq : i = ⟨i.val, h1⟩ := by ext; rfl
      rw [heq, nfa_run_penultimate_fiber_get_append_left_elem w a j h1]
      exact hj_step
    · have hi_eq : i.val = w.length := by
        have hi_lt : i.val < (w ++ [a]).length := i.isLt
        have : (w ++ [a]).length = w.length + 1 := by simp
        omega
      have hcast_le : i.castSucc.val ≤ w.length := by
        have : i.castSucc.val = i.val := rfl
        omega
      have hsucc_gt : ¬ i.succ.val ≤ w.length := by
        have : i.succ.val = i.val + 1 := rfl
        omega
      rw [nfa_run_penultimate_fiber_from_r0_of_le w a q r0 _ hcast_le, nfa_run_penultimate_fiber_from_r0_of_gt w a q r0 _ hsucc_gt]
      have hj_cast : (⟨i.castSucc.val, Nat.lt_succ_of_le hcast_le⟩ : Fin (w.length + 1)) = Fin.last w.length := by
        ext; exact hi_eq
      rw [hj_cast, hr0_last]
      have h1 : w.length < (w ++ [a]).length := by
        have : (w ++ [a]).length = w.length + 1 := by simp
        omega
      have heq : i = ⟨w.length, h1⟩ := by ext; exact hi_eq
      rw [heq, nfa_run_penultimate_fiber_get_append_last_elem w a h1]
      exact hq
  · have hle : (⟨w.length, by simp⟩ : Fin ((w ++ [a]).length + 1)).val ≤ w.length := le_refl _
    rw [nfa_run_penultimate_fiber_from_r0_of_le w a q r0 _ hle]
    have : (⟨(⟨w.length, by simp⟩ : Fin ((w ++ [a]).length + 1)).val, Nat.lt_succ_of_le hle⟩ : Fin (w.length + 1)) =
      Fin.last w.length := by ext; rfl
    rw [this, hr0_last]

open Classical in
/-- The number of runs of w ++ [a] from p to q with penultimate state s equals the number of runs of w from p to s if q ∈ M.step s a, and 0 otherwise. -/
theorem nfa_run_penultimate_fiber {α σ : Type*} [Fintype σ] (M : NFA α σ) (w : List α) (a : α)
    (p q s : σ) :
    {r : Fin ((w ++ [a]).length + 1) → σ |
      r 0 = p ∧ r (Fin.last (w ++ [a]).length) = q ∧
      (∀ i : Fin (w ++ [a]).length, r i.succ ∈ M.step (r i.castSucc) ((w ++ [a]).get i)) ∧
      r ⟨w.length, by simp⟩ = s}.ncard
    = if q ∈ M.step s a then nfa_run_count_list M w p s else 0 := by
  let A := {r : Fin ((w ++ [a]).length + 1) → σ |
      r 0 = p ∧ r (Fin.last (w ++ [a]).length) = q ∧
      (∀ i : Fin (w ++ [a]).length, r i.succ ∈ M.step (r i.castSucc) ((w ++ [a]).get i)) ∧
      r ⟨w.length, by simp⟩ = s}
  let B := {r0 : Fin (w.length + 1) → σ |
      r0 0 = p ∧ r0 (Fin.last w.length) = s ∧
      ∀ i : Fin w.length, r0 i.succ ∈ M.step (r0 i.castSucc) (w.get i)}
  change A.ncard = if q ∈ M.step s a then B.ncard else 0
  split_ifs with hq
  · have h_inv : Set.InvOn (nfa_run_penultimate_fiber_from_r0 w a q) (nfa_run_penultimate_fiber_to_r0 w a) A B := by
      refine ⟨fun r hr => nfa_run_penultimate_fiber_from_to_r0 w a q r hr.2.1, fun r0 hr0 => nfa_run_penultimate_fiber_to_from_r0 w a q r0⟩
    have h_maps : Set.MapsTo (nfa_run_penultimate_fiber_to_r0 w a) A B := by
      intro r hr
      exact nfa_run_penultimate_fiber_to_r0_mem M w a p s hr.1 hr.2.2.1 hr.2.2.2
    have h_maps_inv : Set.MapsTo (nfa_run_penultimate_fiber_from_r0 w a q) B A := by
      intro r0 hr0
      exact nfa_run_penultimate_fiber_from_r0_mem M w a p q s hr0.1 hr0.2.1 hr0.2.2 hq
    have h_bij : Set.BijOn (nfa_run_penultimate_fiber_to_r0 w a) A B := Set.InvOn.bijOn h_inv h_maps h_maps_inv
    exact Set.BijOn.ncard_eq h_bij
  · have h_empty : A = ∅ := by
      ext r
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hr
      have : q ∈ M.step s a := nfa_run_penultimate_fiber_to_r0_step_last M w a q s hr.2.1 hr.2.2.1 hr.2.2.2
      exact hq this
    rw [h_empty, Set.ncard_empty]
