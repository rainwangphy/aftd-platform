import AFTD.Prelude
import AFTD.Kb.Tcs.HashProbeExpectedCost
import AFTD.Kb.Tcs.HashProbeTailProb
import AFTD.Kb.Tcs.HashProbeTailCount
import AFTD.Kb.Tcs.HashOccupiedSlots
import AFTD.Kb.Tcs.HashInsertStep
import AFTD.Kb.Tcs.HashProbeTailProbZero
import AFTD.Kb.Tcs.HashOccupiedSlotsNil
import AFTD.Kb.Tcs.HashOccupiedSlotsCard

/-!
# hash_probe_expected_cost_two

Topic: data_structures   Node: 89b71b668f5c

Provenance: helper lemma. Unit-first fixed-offset mean-probe extremality; experiments 11670–11680 and arXiv:2610.31363.

After two insertions the expected cost is 1+2/n+(3+[2r₁=0])/n².
-/

open scoped BigOperators

private lemma hx_occ_append (n : ℕ) (r : Fin n → ZMod n)
    (A : List (ZMod n)) (a : ZMod n) :
    hash_occupied_slots n r (A ++ [a]) = hash_insert_step n r (hash_occupied_slots n r A) a := by
  unfold hash_occupied_slots
  rw [List.foldl_append]
  rfl

private lemma hx_insert_not_mem (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (hr0 : r 0 = 0)
    (T : Finset (ZMod n)) (a : ZMod n) (ha : a ∉ T) :
    hash_insert_step n r T a = T ∪ {a} := by
  dsimp only [hash_insert_step]
  have h0 : (0 : Fin n) ∈ (Finset.univ.filter (fun j : Fin n => a + r j ∉ T)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [hr0] using ha
  have hne : (Finset.univ.filter (fun j : Fin n => a + r j ∉ T)).Nonempty := ⟨0, h0⟩
  rw [dif_pos hne]
  congr 1
  have hmin : (Finset.univ.filter (fun j : Fin n => a + r j ∉ T)).min' hne = 0 := by
    apply le_antisymm _ (Fin.zero_le _)
    exact Finset.min'_le _ _ h0
  rw [hmin]
  simp [hr0]

private lemma hx_occ_single (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (hr0 : r 0 = 0)
    (a : ZMod n) : hash_occupied_slots n r [a] = {a} := by
  have h := hx_occ_append n r ([] : List (ZMod n)) a
  simp only [List.nil_append] at h
  rw [h, hash_occupied_slots_nil]
  rw [hx_insert_not_mem n r hr0 ∅ a (by simp)]
  simp

private lemma hx_occ_two (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (hr0 : r 0 = 0)
    (a b : ZMod n) : hash_occupied_slots n r [a, b] = hash_insert_step n r {a} b := by
  have h := hx_occ_append n r [a] b
  simp only [List.cons_append, List.nil_append] at h
  rw [h, hx_occ_single n r hr0 a]

private lemma hx_occ_two_ne (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (hr0 : r 0 = 0)
    (a b : ZMod n) (hab : a ≠ b) :
    hash_occupied_slots n r [a, b] = {a, b} := by
  rw [hx_occ_two n r hr0 a b]
  rw [hx_insert_not_mem n r hr0 {a} b (by simpa [eq_comm] using hab)]
  simp

private lemma hx_occ_two_eq (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (hr : Function.Bijective r)
    (hr0 : r 0 = 0) (hn : 2 < n) (a : ZMod n) :
    hash_occupied_slots n r [a, a] = {a, a + r 1} := by
  rw [hx_occ_two n r hr0 a a]
  dsimp only [hash_insert_step]
  have hset : (Finset.univ.filter (fun j : Fin n => a + r j ∉ ({a} : Finset (ZMod n))))
      = Finset.univ.erase (0 : Fin n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hj
      refine ⟨?_, trivial⟩
      intro hj0
      subst hj0
      exact hj (by simp [hr0])
    · rintro ⟨hj0, -⟩ hmem
      have hrj : r j = 0 := by
        have hEq : a + r j = a + 0 := by simpa using hmem
        exact add_left_cancel hEq
      exact hj0 (hr.injective (by rw [hrj, hr0]))
  have h1mem : (1 : Fin n) ∈ Finset.univ.erase (0 : Fin n) := by
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at h'
    omega
  have hne : (Finset.univ.erase (0 : Fin n)).Nonempty := ⟨1, h1mem⟩
  rw [hset, dif_pos hne]
  have hmin : (Finset.univ.erase (0 : Fin n)).min' hne = 1 := by
    rw [Finset.min'_eq_iff]
    refine ⟨h1mem, ?_⟩
    intro b hb
    rw [Finset.mem_erase] at hb
    obtain ⟨hb0, -⟩ := hb
    rw [Fin.le_def]
    have hbval : b.val ≠ 0 := by simpa using hb0
    have h1 : (1 : Fin n).val = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    omega
  rw [hmin]
  simp

private lemma hx_sum_pair (n : ℕ) [NeZero n] (d a b : ZMod n) (hd : d ≠ 0) (hab : a ≠ b) :
    (∑ h : ZMod n, if h ∈ ({a, b} : Finset (ZMod n)) ∧ h + d ∈ ({a, b} : Finset (ZMod n))
      then (1 : ℕ) else 0)
      = (if a + d = b then 1 else 0) + (if b + d = a then 1 else 0) := by
  have hcongr : ∀ h : ZMod n,
      (if h ∈ ({a, b} : Finset (ZMod n)) ∧ h + d ∈ ({a, b} : Finset (ZMod n)) then (1 : ℕ) else 0)
        = if h ∈ ({a, b} : Finset (ZMod n))
            then (if h + d ∈ ({a, b} : Finset (ZMod n)) then (1 : ℕ) else 0) else 0 := by
    intro h; by_cases hh : h ∈ ({a, b} : Finset (ZMod n)) <;> simp [hh]
  simp_rw [hcongr]
  rw [Finset.sum_ite_mem]
  simp only [Finset.univ_inter]
  rw [Finset.sum_pair hab]
  have had : a + d ≠ a := by
    intro hh; apply hd
    have hEq : a + d = a + 0 := by simpa using hh
    exact add_left_cancel hEq
  have hbd : b + d ≠ b := by
    intro hh; apply hd
    have hEq : b + d = b + 0 := by simpa using hh
    exact add_left_cancel hEq
  simp only [Finset.mem_insert, Finset.mem_singleton, had, hbd, false_or, or_false]

private lemma hx_sum_single (n : ℕ) [NeZero n] (d a : ZMod n) (hd : d ≠ 0) :
    (∑ h : ZMod n, if h ∈ ({a, a + d} : Finset (ZMod n)) ∧ h + d ∈ ({a, a + d} : Finset (ZMod n))
      then (1 : ℕ) else 0)
      = 1 + (if d + d = 0 then 1 else 0) := by
  have hneq : a ≠ a + d := by
    intro hh; apply hd
    have hEq : a + d = a + 0 := by simpa [eq_comm] using hh
    exact add_left_cancel hEq
  have hcongr : ∀ h : ZMod n,
      (if h ∈ ({a, a + d} : Finset (ZMod n)) ∧ h + d ∈ ({a, a + d} : Finset (ZMod n))
        then (1 : ℕ) else 0)
        = if h ∈ ({a, a + d} : Finset (ZMod n))
            then (if h + d ∈ ({a, a + d} : Finset (ZMod n)) then (1 : ℕ) else 0) else 0 := by
    intro h; by_cases hh : h ∈ ({a, a + d} : Finset (ZMod n)) <;> simp [hh]
  simp_rw [hcongr]
  rw [Finset.sum_ite_mem]
  simp only [Finset.univ_inter]
  rw [Finset.sum_pair hneq]
  have hfirst : (if a + d ∈ ({a, a + d} : Finset (ZMod n)) then (1 : ℕ) else 0) = 1 := by
    simp
  rw [hfirst]
  congr 1
  have hiff : ((a + d) + d ∈ ({a, a + d} : Finset (ZMod n))) ↔ (d + d = 0) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · have hEq : a + (d + d) = a + 0 := by
          calc a + (d + d) = (a + d) + d := by abel
            _ = a := h
          simpa using hEq
        exact add_left_cancel hEq
      · exfalso
        have hEq : (a + d) + d = (a + d) + 0 := by
          simpa [eq_comm] using h
        have hzero : d = 0 := add_left_cancel hEq
        exact hd hzero
    · intro hh
      left
      calc (a + d) + d = a + (d + d) := by abel
        _ = a + 0 := by rw [hh]
        _ = a := by abel
  by_cases hdd : d + d = 0
  · rw [if_pos hdd, if_pos (hiff.mpr hdd)]
  · rw [if_neg hdd, if_neg (fun h => hdd (hiff.mp h))]

private lemma hx_cond (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (hr0 : r 0 = 0) (hn : 2 < n)
    (A : Fin 2 → ZMod n) (h : ZMod n) :
    (∀ j : Fin n, j.val < 2 → h + r j ∈ hash_occupied_slots n r (List.ofFn A))
      ↔ h ∈ hash_occupied_slots n r (List.ofFn A)
        ∧ h + r 1 ∈ hash_occupied_slots n r (List.ofFn A) := by
  constructor
  · intro hh
    refine ⟨?_, ?_⟩
    · simpa [hr0] using hh 0 (by simp)
    · exact hh 1 (by
        rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
        omega)
  · rintro ⟨h0, h1⟩ j hj
    have hj' : j.val = 0 ∨ j.val = 1 := by omega
    rcases hj' with hj0 | hj1
    · have hjeq : j = 0 := Fin.ext hj0
      subst hjeq
      simpa [hr0] using h0
    · have hjeq : j = 1 := by
        apply Fin.ext
        rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
        exact hj1
      subst hjeq
      exact h1

private lemma hx_inner (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (hr : Function.Bijective r)
    (hr0 : r 0 = 0) (hn : 2 < n) (hd : r 1 ≠ 0) (a b : ZMod n) :
    (∑ h : ZMod n, if h ∈ hash_occupied_slots n r [a, b] ∧ h + r 1 ∈ hash_occupied_slots n r [a, b]
      then (1 : ℕ) else 0)
      = (if a = b then 1 else 0)
        + (if a = b then (if r 1 + r 1 = 0 then 1 else 0) else 0)
        + (if a + r 1 = b then 1 else 0)
        + (if b + r 1 = a then 1 else 0) := by
  by_cases hab : a = b
  · subst hab
    rw [hx_occ_two_eq n r hr hr0 hn a]
    rw [hx_sum_single n (r 1) a hd]
    have had : a + r 1 ≠ a := by
      intro hh; apply hd
      have hEq : a + r 1 = a + 0 := by simpa using hh
      exact add_left_cancel hEq
    simp [had]
  · rw [hx_occ_two_ne n r hr0 a b hab]
    rw [hx_sum_pair n (r 1) a b hd hab]
    simp [hab]

private lemma hx_sum_arrow (n : ℕ) [NeZero n] (f : ZMod n → ZMod n → ℕ) :
    (∑ A : Fin 2 → ZMod n, f (A 0) (A 1)) = ∑ a, ∑ b, f a b := by
  rw [← Fintype.sum_prod_type (fun p : ZMod n × ZMod n => f p.1 p.2)]
  apply Fintype.sum_equiv (finTwoArrowEquiv (ZMod n))
  intro A
  simp [finTwoArrowEquiv]

private lemma hx_occ_card (n : ℕ) [NeZero n] (r : Fin n → ZMod n)
    (hr : Function.Bijective r) (hn : 2 < n) (A : Fin 2 → ZMod n) :
    (hash_occupied_slots n r (List.ofFn A)).card = 2 := by
  rw [hash_occupied_slots_card n r hr (List.ofFn A) (by rw [List.length_ofFn]; omega)]
  rw [List.length_ofFn]

private lemma hx_one_ne_zero (n : ℕ) [NeZero n] (hn : 2 < n) (r : Fin n → ZMod n)
    (hr : Function.Bijective r) (hr0 : r 0 = 0) : r 1 ≠ 0 := by
  intro h
  have h1 : (1 : Fin n) = 0 := hr.injective (by rw [h, hr0])
  have h2 := congrArg Fin.val h1
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega), Fin.val_zero] at h2
  omega

private lemma hx_two_ne_zero (n : ℕ) [NeZero n] (hn : 2 < n) (r : Fin n → ZMod n)
    (hr : Function.Bijective r) (hr0 : r 0 = 0) : r 2 ≠ 0 := by
  intro h
  have h1 : (2 : Fin n) = 0 := hr.injective (by rw [h, hr0])
  have h2 := congrArg Fin.val h1
  have h2val : (2 : Fin n).val = 2 := by
    show 2 % n = 2
    exact Nat.mod_eq_of_lt (by omega)
  rw [h2val, Fin.val_zero] at h2
  omega

private lemma hx_one_ne_two (n : ℕ) [NeZero n] (hn : 2 < n) (r : Fin n → ZMod n)
    (hr : Function.Bijective r) : r 1 ≠ r 2 := by
  intro h
  have h1 : (1 : Fin n) = 2 := hr.injective h
  have h2 := congrArg Fin.val h1
  have h2val : (2 : Fin n).val = 2 := by
    show 2 % n = 2
    exact Nat.mod_eq_of_lt (by omega)
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega), h2val] at h2
  omega

private lemma hx_tail_count_two (n : ℕ) [NeZero n] (r : Fin n → ZMod n)
    (hr : Function.Bijective r) (hr0 : r 0 = 0) (hn : 2 < n) (hd : r 1 ≠ 0) :
    hash_probe_tail_count n r 2 2 = n * (3 + (if r 1 + r 1 = 0 then 1 else 0)) := by
  unfold hash_probe_tail_count
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only [hx_cond n r hr0 hn]
  have hofn : ∀ A : Fin 2 → ZMod n, List.ofFn A = [A 0, A 1] := fun A => by simp [List.ofFn_succ]
  simp only [hofn]
  rw [hx_sum_arrow n (fun a b => ∑ h : ZMod n,
    if h ∈ hash_occupied_slots n r [a, b] ∧ h + r 1 ∈ hash_occupied_slots n r [a, b]
      then (1 : ℕ) else 0)]
  simp only [hx_inner n r hr hr0 hn hd]
  have hstep : ∀ a : ZMod n,
      (Finset.univ.sum (fun b : ZMod n => (((if a = b then (1:ℕ) else 0)
        + (if a = b then (if r 1 + r 1 = 0 then (1:ℕ) else 0) else 0))
        + (if a + r 1 = b then (1:ℕ) else 0)) + (if b + r 1 = a then (1:ℕ) else 0)))
      = 3 + (if r 1 + r 1 = 0 then (1:ℕ) else 0) := by
    intro a
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 : (∑ b : ZMod n, if a = b then (1:ℕ) else 0) = 1 := by simp
    have h2 : (∑ b : ZMod n, if a = b then (if r 1 + r 1 = 0 then (1:ℕ) else 0) else 0)
        = (if r 1 + r 1 = 0 then (1:ℕ) else 0) := by simp
    have h3 : (∑ b : ZMod n, if a + r 1 = b then (1:ℕ) else 0) = 1 := by simp
    have h4 : (∑ b : ZMod n, if b + r 1 = a then (1:ℕ) else 0) = 1 := by
      rw [show (∑ b : ZMod n, if b + r 1 = a then (1:ℕ) else 0)
            = ∑ b : ZMod n, if b = a - r 1 then (1:ℕ) else 0 from by
        apply Finset.sum_congr rfl
        intro b _
        by_cases h : b + r 1 = a
        · have hb : b = a - r 1 := by rw [← h]; abel
          simp [hb]
        · have hb : b ≠ a - r 1 := by
            intro hh; exact h (by rw [hh]; abel)
          simp [h, hb]]
      simp
    rw [h1, h2, h3, h4]
    omega
  simp only [hstep]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card]
  simp

private lemma hx_tail_count_one (n : ℕ) [NeZero n] (r : Fin n → ZMod n)
    (hr : Function.Bijective r) (hr0 : r 0 = 0) (hn : 2 < n) :
    hash_probe_tail_count n r 2 1 = 2 * n ^ 2 := by
  unfold hash_probe_tail_count
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have hcond : ∀ (A : Fin 2 → ZMod n) (h : ZMod n),
      ((∀ j : Fin n, j.val < 1 → h + r j ∈ hash_occupied_slots n r (List.ofFn A))
        ↔ h ∈ hash_occupied_slots n r (List.ofFn A)) := by
    intro A h
    constructor
    · intro hh
      simpa [hr0] using hh 0 (by simp)
    · intro hh j hj
      have hj0 : j.val = 0 := by omega
      have hjeq : j = 0 := Fin.ext hj0
      subst hjeq
      simpa [hr0] using hh
  simp only [hcond]
  have hstep : ∀ A : Fin 2 → ZMod n,
      (∑ h : ZMod n, if h ∈ hash_occupied_slots n r (List.ofFn A) then (1:ℕ) else 0) = 2 := by
    intro A
    rw [← Finset.card_filter]
    have h2 : Finset.univ.filter (fun h : ZMod n => h ∈ hash_occupied_slots n r (List.ofFn A))
        = hash_occupied_slots n r (List.ofFn A) := by ext h; simp
    rw [h2]
    exact hx_occ_card n r hr hn A
  simp only [hstep]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  simp [mul_comm]

private lemma hx_tail_count_three (n : ℕ) [NeZero n] (r : Fin n → ZMod n)
    (hr : Function.Bijective r) (hr0 : r 0 = 0) (hn : 2 < n) {k : ℕ} (hk : 3 ≤ k) :
    hash_probe_tail_count n r 2 k = 0 := by
  unfold hash_probe_tail_count
  rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨⟨A, x⟩, hp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hr1 := hx_one_ne_zero n hn r hr hr0
  have hr2 := hx_two_ne_zero n hn r hr hr0
  have hr12 := hx_one_ne_two n hn r hr
  have h2val : (2 : Fin n).val = 2 := by
    show 2 % n = 2
    exact Nat.mod_eq_of_lt (by omega)
  have h0val : (0 : Fin n).val = 0 := by simp
  have m0 : x + r 0 ∈ hash_occupied_slots n r (List.ofFn A) := hp 0 (by rw [h0val]; omega)
  have m1 : x + r 1 ∈ hash_occupied_slots n r (List.ofFn A) :=
    hp 1 (by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]; omega)
  have m2 : x + r 2 ∈ hash_occupied_slots n r (List.ofFn A) := hp 2 (by rw [h2val]; omega)
  have e01 : x + r 0 ≠ x + r 1 := by
    intro hh
    have h00 : r 0 = r 1 := add_left_cancel hh
    rw [hr0] at h00
    exact hr1 h00.symm
  have e02 : x + r 0 ≠ x + r 2 := by
    intro hh
    have h00 : r 0 = r 2 := add_left_cancel hh
    rw [hr0] at h00
    exact hr2 h00.symm
  have e12 : x + r 1 ≠ x + r 2 := fun hh => hr12 (add_left_cancel hh)
  have hsub : ({x + r 0, x + r 1, x + r 2} : Finset (ZMod n)) ⊆
      hash_occupied_slots n r (List.ofFn A) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h
    · subst h; exact m0
    · subst h; exact m1
    · subst h; exact m2
  have hcard3 : ({x + r 0, x + r 1, x + r 2} : Finset (ZMod n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [e01, e02]),
      Finset.card_insert_of_notMem (by simp [e12]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  rw [hcard3, hx_occ_card n r hr hn A] at hle
  omega

theorem hash_probe_expected_cost_two (n : ℕ) [NeZero n] (hn : 2 < n)
  (r : Fin n → ZMod n) (hr : Function.Bijective r) (hr0 : r 0 = 0) :
  hash_probe_expected_cost n r 2 =
    1 + 2 / (n : ℝ) + (3 + (if r 1 + r 1 = 0 then (1 : ℝ) else 0)) / (n : ℝ)^2 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have h : n ≠ 0 := NeZero.ne n
    positivity
  have hd : r 1 ≠ 0 := hx_one_ne_zero n hn r hr hr0
  have h0 : hash_probe_tail_prob n r 2 0 = 1 := hash_probe_tail_prob_zero n r 2
  have h1 : hash_probe_tail_prob n r 2 1 = 2 / (n : ℝ) := by
    rw [hash_probe_tail_prob, hx_tail_count_one n r hr hr0 hn]
    push_cast
    rw [show (n : ℝ) ^ 3 = (n : ℝ) ^ 2 * (n : ℝ) by ring]
    field_simp
  have h2 : hash_probe_tail_prob n r 2 2
      = (3 + (if r 1 + r 1 = 0 then (1 : ℝ) else 0)) / (n : ℝ)^2 := by
    rw [hash_probe_tail_prob, hx_tail_count_two n r hr hr0 hn hd]
    by_cases hh : r 1 + r 1 = 0
    · simp only [if_pos hh]
      have e1 : ((n * (3 + 1) : ℕ) : ℝ) = (n : ℝ) * 4 := by push_cast; ring
      rw [e1, show (n : ℝ) ^ 3 = (n : ℝ) * (n : ℝ) ^ 2 by ring]
      field_simp
      norm_num
    · simp only [if_neg hh]
      have e1 : ((n * 3 : ℕ) : ℝ) = (n : ℝ) * 3 := by push_cast; ring
      rw [e1, show (n : ℝ) ^ 3 = (n : ℝ) * (n : ℝ) ^ 2 by ring]
      field_simp
      norm_num
  unfold hash_probe_expected_cost
  have hsub : ({0, 1, 2} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_range]
    rcases hx with h | h | h <;> omega
  have hzero : ∀ x ∈ Finset.range (n + 1), x ∉ ({0, 1, 2} : Finset ℕ) →
      hash_probe_tail_prob n r 2 x = 0 := by
    intro x _ hx2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx2
    have hx3 : 3 ≤ x := by omega
    rw [hash_probe_tail_prob, hx_tail_count_three n r hr hr0 hn hx3]
    simp
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  rw [h0, h1, h2]
  ring
