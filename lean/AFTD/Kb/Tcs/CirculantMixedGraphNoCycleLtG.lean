import AFTD.Prelude
import AFTD.Kb.Tcs.MixedGraphHasCycle
import AFTD.Kb.Tcs.CirculantCycleValSubSumDvd
import AFTD.Kb.Tcs.CirculantCycleNotAllEdgeSteps
import AFTD.Kb.Tcs.CirculantCycleRemainderBound

/-!
# circulant_mixed_graph_no_cycle_lt_g

Topic: graphs   Node: f65bb69911ae

Provenance: helper lemma. step towards mixed_cage_order_one_le

For z ≥ 1 and g ≥ 3, the circulant mixed graph on N(z, g) vertices contains no mixed cycle of length t < g.
-/

lemma circulant_mixed_graph_no_cycle_lt_g_val_sub_eq_m_of_rev {N m : ℕ} (hN : N = 2 * m) (hm : 0 < m) {a b : Fin N}
    (h : (a - b).val = m) : (b - a).val = m := by
  have hmN : m < N := by omega
  have h1 : a.val ≡ b.val + m [MOD N] := circulant_cycle_not_all_edge_steps_step hN hm h
  have h2 : b.val ≡ a.val + m [MOD N] := by
    have h1' : b.val + m + m ≡ a.val + m [MOD N] := (Nat.ModEq.add_right m h1).symm
    have h2' : b.val + m + m = b.val + N := by omega
    have h3' : b.val + N ≡ b.val [MOD N] := by
      have : N ≡ 0 [MOD N] := by rw [Nat.ModEq, Nat.mod_self, Nat.zero_mod]
      have := Nat.ModEq.add (Nat.ModEq.refl b.val) this
      omega
    rw [h2'] at h1'
    exact h3'.symm.trans h1'
  rw [Fin.val_sub]
  have hmod : (N - a.val + b.val) ≡ m [MOD N] := by
    have : N - a.val + b.val ≡ N - a.val + (a.val + m) [MOD N] := Nat.ModEq.add_left (N - a.val) h2
    have heq : N - a.val + (a.val + m) = N + m := by omega
    rw [heq] at this
    have hN0 : N ≡ 0 [MOD N] := by rw [Nat.ModEq, Nat.mod_self, Nat.zero_mod]
    have hm' : N + m ≡ 0 + m [MOD N] := Nat.ModEq.add_right m hN0
    rw [zero_add] at hm'
    exact this.trans hm'
  rw [Nat.ModEq] at hmod
  rw [hmod]
  exact Nat.mod_eq_of_lt hmN

lemma circulant_mixed_graph_no_cycle_lt_g_div_mod_cases (z m d : ℕ) (hz : 1 ≤ z) (hzm : z < m)
    (hd : d = m ∨ (1 ≤ d ∧ d ≤ (z + 1) / 2) ∨ (m + 1 ≤ d ∧ d ≤ m + z / 2)) :
    d / m ≤ 1 ∧ d % m ≤ (z + 1) / 2 ∧ (d / m = 1 → d % m ≤ z / 2) ∧ (d % m = 0 → d = m) := by
  have hm : 0 < m := by omega
  rcases hd with rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [Nat.div_self hm, Nat.mod_self]
    omega
  · have hdm : d < m := by omega
    rw [Nat.div_eq_of_lt hdm, Nat.mod_eq_of_lt hdm]
    omega
  · have hdm_lt : d - m < m := by omega
    have heq : d = (d - m) + m := by omega
    rw [heq, Nat.add_div_right (d - m) hm, Nat.add_mod_right,
        Nat.div_eq_of_lt hdm_lt, Nat.mod_eq_of_lt hdm_lt]
    omega

/-- The circulant mixed graph M(z, g) has no mixed cycle of length shorter than g. -/
theorem circulant_mixed_graph_no_cycle_lt_g (z g : ℕ) (hz : 1 ≤ z) (hg : 3 ≤ g) :
    let N := if Even z then z * (g - 1) + 2 else (z + 1) * (g - 1)
    let m := N / 2
    let E := SimpleGraph.fromRel fun (x y : Fin N) => (y - x).val = m
    let A : Fin N → Fin N → Prop := fun x y =>
      (1 ≤ (y - x).val ∧ (y - x).val ≤ (z + 1) / 2) ∨
      (m + 1 ≤ (y - x).val ∧ (y - x).val ≤ m + z / 2)
    ∀ t < g, ¬mixed_graph_has_cycle E A t := by
  intro N m E A t htg hcycle
  have ht3 : 3 ≤ t := hcycle.1
  obtain ⟨x, hinj, hstep⟩ := hcycle.2
  have hg1 : 2 ≤ g - 1 := by omega
  have hN_even : Even N := by
    by_cases hze : Even z
    · dsimp [N]; simp only [hze, if_true]
      exact Even.add (hze.mul_right (g - 1)) even_two
    · dsimp [N]; simp only [hze, if_false]
      have hodd : Odd z := Nat.not_even_iff_odd.mp hze
      exact (hodd.add_one).mul_right (g - 1)
  have hN_ge : 2 * (z + 1) ≤ N := by
    by_cases hze : Even z
    · dsimp [N]; simp only [hze, if_true]
      have h2 : z * 2 ≤ z * (g - 1) := Nat.mul_le_mul_left z hg1
      omega
    · dsimp [N]; simp only [hze, if_false]
      have h2 : (z + 1) * 2 ≤ (z + 1) * (g - 1) := Nat.mul_le_mul_left (z + 1) hg1
      omega
  have hNm : N = 2 * m := by
    dsimp [m]
    have h := Nat.div_two_mul_two_of_even hN_even
    omega
  have hzm : z < m := by
    dsimp [m]
    have h1 : (2 * (z + 1)) / 2 ≤ N / 2 := Nat.div_le_div_right hN_ge
    rw [Nat.mul_div_right (z + 1) (by norm_num : 0 < 2)] at h1
    omega
  have hm : 0 < m := by omega
  let d : Fin t → ℕ := fun i => (x (finRotate t i) - x i).val
  have hd_cases : ∀ i, d i = m ∨ (1 ≤ d i ∧ d i ≤ (z + 1) / 2) ∨ (m + 1 ≤ d i ∧ d i ≤ m + z / 2) := by
    intro i
    rcases hstep i with hE | hA
    · rw [SimpleGraph.fromRel_adj] at hE
      rcases hE.2 with h1 | h2
      · left; exact h1
      · left; exact circulant_mixed_graph_no_cycle_lt_g_val_sub_eq_m_of_rev hNm hm h2
    · right; exact hA
  let q : Fin t → ℕ := fun i => d i / m
  let r : Fin t → ℕ := fun i => d i % m
  have hprops : ∀ i, q i ≤ 1 ∧ r i ≤ (z + 1) / 2 ∧ (q i = 1 → r i ≤ z / 2) ∧ (r i = 0 → d i = m) := by
    intro i
    exact circulant_mixed_graph_no_cycle_lt_g_div_mod_cases z m (d i) hz hzm (hd_cases i)
  have hq : ∀ i, q i ≤ 1 := fun i => (hprops i).1
  have hr : ∀ i, r i ≤ (z + 1) / 2 := fun i => (hprops i).2.1
  have hr_q : ∀ i, q i = 1 → r i ≤ z / 2 := fun i => (hprops i).2.2.1
  have hr_zero : ∀ i, r i = 0 → d i = m := fun i => (hprops i).2.2.2
  have hbound := circulant_cycle_remainder_bound z g t hz hg htg q r hq hr hr_q
  have hR_le : (∑ i, r i) ≤ m := hbound.1
  have hOdd_Q : Odd (∑ i, q i) → (∑ i, r i) < m := hbound.2
  have hd_eq : ∀ i, d i = q i * m + r i := by
    intro i
    dsimp [q, r]
    rw [mul_comm, Nat.div_add_mod]
  have hsum_d : (∑ i, d i) = (∑ i, q i) * m + (∑ i, r i) := by
    have : (∑ i, d i) = ∑ i, (q i * m + r i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hd_eq i
    rw [this, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hdvd : N ∣ ∑ i, d i := circulant_cycle_val_sub_sum_dvd x
  rw [hNm, hsum_d] at hdvd
  have h_m_dvd_R : m ∣ (∑ i, r i) := by
    have h1 : m ∣ 2 * m := dvd_mul_left m 2
    have h2 : m ∣ (∑ i, q i) * m + (∑ i, r i) := dvd_trans h1 hdvd
    have h3 : m ∣ (∑ i, q i) * m := dvd_mul_left m (∑ i, q i)
    exact (Nat.dvd_add_right h3).mp h2
  have hR_cases : (∑ i, r i) = 0 ∨ (∑ i, r i) = m := by
    obtain ⟨k, hk⟩ := h_m_dvd_R
    cases k with
    | zero => left; omega
    | succ k =>
      cases k with
      | zero => right; omega
      | succ k =>
        exfalso
        have h1 : m * 2 ≤ m * (k + 1 + 1) := Nat.mul_le_mul_left m (by omega)
        have h2 : m * 2 ≤ ∑ i, r i := by omega
        have h3 : m * 2 ≤ m := h2.trans hR_le
        omega
  rcases hR_cases with hR0 | hRm
  · have hall_m : ∀ i, d i = m := by
      intro i
      have hri : r i = 0 := by
        have := Finset.single_le_sum (fun j _ => Nat.zero_le (r j)) (Finset.mem_univ i)
        omega
      exact hr_zero i hri
    exact circulant_cycle_not_all_edge_steps ht3 hNm hm x hinj hall_m
  · rw [hRm] at hdvd
    have heq : (∑ i, q i) * m + m = ((∑ i, q i) + 1) * m := by ring
    rw [heq] at hdvd
    have hdvd2 : 2 ∣ (∑ i, q i) + 1 := (Nat.mul_dvd_mul_iff_right hm).mp hdvd
    obtain ⟨k, hk⟩ := hdvd2
    have hodd : Odd (∑ i, q i) := Nat.odd_iff.mpr (by omega)
    have hlt : (∑ i, r i) < m := hOdd_Q hodd
    omega
