import AFTD.Prelude
import AFTD.Kb.Tcs.HasDegreeLe
import AFTD.Kb.Tcs.BentSumCounterexampleFunc

/-!
# bent_sum_counterexample_not_has_degree_lt

Topic: cryptography   Node: 6c9feb4ff7f8

Provenance: helper lemma. step towards bent_sum_counterexample_not_sum_of_two_bent

For any m ≥ 4 and any k < m, bent_sum_counterexample_func m hm does not have algebraic degree at most k.
-/

lemma bent_sum_counterexample_not_has_degree_lt_prod_T (m : ℕ) (hm : 4 ≤ m) (x : Fin (2 * m) → ZMod 2) :
    let S0 : Finset (Fin (2 * m)) := Finset.univ.image (fun (i : Fin (m - 2)) => ⟨i.val, by omega⟩)
    let a : Fin (2 * m) := ⟨m - 2, by omega⟩
    let b : Fin (2 * m) := ⟨m - 1, by omega⟩
    let T : Finset (Fin (2 * m)) := insert a (insert b S0)
    (∏ i ∈ T, x i) = (∏ i : Fin (m - 2), x ⟨i.val, by omega⟩) * (x a * x b) := by
  intro S0 a b T
  have hS0_mem : ∀ v ∈ S0, (v : Fin (2 * m)).val < m - 2 := by
    intro v hv
    simp only [S0, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨i, hi⟩
    have hi_val : (v : ℕ) = i.val := congrArg Fin.val hi.symm
    have := i.isLt; omega
  have hb_notin_S0 : b ∉ S0 := by
    intro h; have := hS0_mem b h; dsimp [b] at this; omega
  have ha_notin_S0 : a ∉ S0 := by
    intro h; have := hS0_mem a h; dsimp [a] at this; omega
  have hab : a ≠ b := by
    intro h; apply_fun Fin.val at h; dsimp [a, b] at h; omega
  have ha_notin : a ∉ insert b S0 := by
    simp [hab, ha_notin_S0]
  have hprod_S0 : (∏ i ∈ S0, x i) = ∏ i : Fin (m - 2), x ⟨i.val, by omega⟩ := by
    dsimp [S0]
    rw [Finset.prod_image]
    intro u _ v _ huv
    ext
    have := congrArg Fin.val huv
    exact this
  dsimp [T]
  rw [Finset.prod_insert ha_notin, Finset.prod_insert hb_notin_S0, hprod_S0]
  ring

/-- The counterexample Boolean function f_n on (Fin (2*m) → ZMod 2) does not have algebraic degree strictly less than m. -/
theorem bent_sum_counterexample_not_has_degree_lt (m : ℕ) (hm : 4 ≤ m) :
    ∀ k < m, ¬ has_degree_le (bent_sum_counterexample_func m hm) k := by
  intro k hk hdeg
  let S0 : Finset (Fin (2 * m)) := Finset.univ.image (fun (i : Fin (m - 2)) => ⟨i.val, by omega⟩)
  let a : Fin (2 * m) := ⟨m - 2, by omega⟩
  let b : Fin (2 * m) := ⟨m - 1, by omega⟩
  let T : Finset (Fin (2 * m)) := insert a (insert b S0)

  have hS0_card : S0.card = m - 2 := by
    dsimp [S0]
    rw [Finset.card_image_of_injective]
    · exact Fintype.card_fin (m - 2)
    · intro x y hxy
      ext
      have : (⟨x.val, by omega⟩ : Fin (2 * m)).val = (⟨y.val, by omega⟩ : Fin (2 * m)).val := congrArg Fin.val hxy
      exact this
  have hS0_mem : ∀ v ∈ S0, (v : Fin (2 * m)).val < m - 2 := by
    intro v hv
    simp only [S0, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨i, hi⟩
    have hi_val : (v : ℕ) = i.val := congrArg Fin.val hi.symm
    have := i.isLt; omega
  have hb_notin_S0 : b ∉ S0 := by
    intro h; have := hS0_mem b h; dsimp [b] at this; omega
  have ha_notin_S0 : a ∉ S0 := by
    intro h; have := hS0_mem a h; dsimp [a] at this; omega
  have hab : a ≠ b := by
    intro h; apply_fun Fin.val at h; dsimp [a, b] at h; omega
  have ha_notin : a ∉ insert b S0 := by
    simp [hab, ha_notin_S0]
  have hT_card : T.card = m := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem ha_notin, Finset.card_insert_of_notMem hb_notin_S0, hS0_card]
    omega

  have hkT : k < T.card := by rw [hT_card]; exact hk

  have h_zero : (∑ A ∈ T.powerset, bent_sum_counterexample_func m hm (fun i => if i ∈ A then 1 else 0)) = 0 := by
    rcases hdeg with ⟨c, hc_card, hc_eval⟩
    have h1 : (∑ A ∈ T.powerset, bent_sum_counterexample_func m hm (fun i => if i ∈ A then 1 else 0)) =
        ∑ A ∈ T.powerset, ∑ S ∈ c, ∏ i ∈ S, (if i ∈ A then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro A hA
      exact hc_eval _
    rw [h1, Finset.sum_comm]
    have h2 : ∀ S ∈ c, (∑ A ∈ T.powerset, ∏ i ∈ S, (if i ∈ A then (1 : ZMod 2) else 0)) = 0 := by
      intro S hS
      have hprod : ∀ A, (∏ i ∈ S, (if i ∈ A then (1 : ZMod 2) else 0)) = if S ⊆ A then 1 else 0 := by
        intro A
        split_ifs with h
        · have : ∀ i ∈ S, (if i ∈ A then (1 : ZMod 2) else 0) = 1 := by
            intro i hi; simp [h hi]
          rw [Finset.prod_congr rfl this, Finset.prod_const_one]
        · rw [Finset.not_subset] at h
          rcases h with ⟨x, hxS, hxA⟩
          have : (if x ∈ A then (1 : ZMod 2) else 0) = 0 := by simp [hxA]
          exact Finset.prod_eq_zero hxS this
      simp_rw [hprod]
      have hScard : S.card < T.card := lt_of_le_of_lt (hc_card S hS) hkT
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      by_cases h : S ⊆ T
      · rw [← Finset.Icc_eq_filter_powerset, Finset.card_Icc_finset h]
        rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Nat.sub_pos_of_lt hScard)) with ⟨r, hr⟩
        rw [hr, pow_succ]
        push_cast
        have : (2 : ZMod 2) = 0 := rfl
        rw [this, mul_zero]
      · have : Finset.filter (fun u => S ⊆ u) T.powerset = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro u hu hsu
          rw [Finset.mem_powerset] at hu
          exact h (hsu.trans hu)
        rw [this, Finset.card_empty, Nat.cast_zero]
    rw [Finset.sum_congr rfl h2, Finset.sum_const_zero]

  have h_one : (∑ A ∈ T.powerset, bent_sum_counterexample_func m hm (fun i => if i ∈ A then 1 else 0)) = 1 := by
    let c1 : Fin (2 * m) := ⟨m, by omega⟩
    let d1 : Fin (2 * m) := ⟨m + 1, by omega⟩
    let e : Fin (2 * m) := ⟨m + 2, by omega⟩
    let f1 : Fin (2 * m) := ⟨m + 3, by omega⟩
    have hT_mem : ∀ v ∈ T, (v : Fin (2 * m)).val ≤ m - 1 := by
      intro v hv
      simp only [T, Finset.mem_insert] at hv
      rcases hv with rfl | rfl | hv
      · dsimp [a]; omega
      · dsimp [b]; omega
      · have := hS0_mem v hv; omega
    have hA_mem : ∀ A ∈ T.powerset, ∀ v ∈ A, (v : Fin (2 * m)).val ≤ m - 1 := by
      intro A hA v hv
      rw [Finset.mem_powerset] at hA
      exact hT_mem v (hA hv)
    have hc1_notin : ∀ A ∈ T.powerset, c1 ∉ A := by
      intro A hA h; have := hA_mem A hA c1 h; dsimp [c1] at this; omega
    have he_notin : ∀ A ∈ T.powerset, e ∉ A := by
      intro A hA h; have := hA_mem A hA e h; dsimp [e] at this; omega
    have h_term : ∀ A ∈ T.powerset,
        bent_sum_counterexample_func m hm (fun i => if i ∈ A then 1 else 0) =
          if A = T then 1 else 0 := by
      intro A hA
      let xA : Fin (2 * m) → ZMod 2 := fun i => if i ∈ A then 1 else 0
      have hxA_c1 : xA c1 = 0 := by dsimp [xA]; simp [hc1_notin A hA]
      have hxA_e : xA e = 0 := by dsimp [xA]; simp [he_notin A hA]
      have hf_def : bent_sum_counterexample_func m hm xA =
          (∏ i : Fin (m - 2), xA ⟨i.val, by omega⟩) * (xA a * xA b + xA c1 * xA d1 + xA e * xA f1) := rfl
      rw [hf_def, hxA_c1, hxA_e, zero_mul, zero_mul, add_zero, add_zero]
      have hpair := bent_sum_counterexample_not_has_degree_lt_prod_T m hm xA
      dsimp only [S0, a, b, T] at hpair
      rw [← hpair]
      have hprod : (∏ i ∈ T, xA i) = if T ⊆ A then 1 else 0 := by
        dsimp [xA]
        split_ifs with h
        · have : ∀ i ∈ T, (if i ∈ A then (1 : ZMod 2) else 0) = 1 := by
            intro i hi; simp [h hi]
          rw [Finset.prod_congr rfl this, Finset.prod_const_one]
        · rw [Finset.not_subset] at h
          rcases h with ⟨v, hvT, hvA⟩
          have : (if v ∈ A then (1 : ZMod 2) else 0) = 0 := by simp [hvA]
          exact Finset.prod_eq_zero hvT this
      rw [hprod]
      rw [Finset.mem_powerset] at hA
      have : (T ⊆ A) ↔ (A = T) := by
        constructor
        · intro h; exact Finset.Subset.antisymm hA h
        · rintro rfl; exact Finset.Subset.refl T
      rw [if_congr this rfl rfl]
    rw [Finset.sum_congr rfl h_term]
    rw [Finset.sum_ite_eq' T.powerset T (fun _ => (1 : ZMod 2))]
    have hT_in : T ∈ T.powerset := Finset.mem_powerset_self T
    simp [hT_in]

  rw [h_zero] at h_one
  exact zero_ne_one h_one
