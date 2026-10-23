import AFTD.Prelude
import AFTD.Kb.Tcs.MixedGraphHasCycle
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# circulant_mixed_graph_cycle_g_exists

Topic: graphs   Node: af23ca800987

Provenance: helper lemma. step towards mixed_cage_order_one_le

For z ≥ 1 and g ≥ 3, the circulant mixed graph on N(z, g) vertices has a mixed cycle of length g: when z is even, g - 1 arc steps of jump z/2 followed by one arc step of jump m + 1; when z is odd, g - 1 arc steps of jump (z+1)/2 followed by one edge step of jump m.
-/

lemma circulant_mixed_graph_cycle_g_exists_sub_eq_of_add_eq {N : ℕ} (x y : Fin N) (h : ℕ)
    (hy : y.val = x.val + h) (hN : x.val + h < N) :
    (y - x).val = h := by
  have _ := hN
  rw [Fin.sub_def]
  dsimp
  have hlt : h < N := by omega
  have : N - x.val + y.val = N + h := by omega
  rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

lemma circulant_mixed_graph_cycle_g_exists_sub_zero_eq {N : ℕ} (x : Fin N)
    (zero : Fin N) (hzero : zero.val = 0) (hx : 0 < x.val) :
    (zero - x).val = N - x.val := by
  rw [Fin.sub_def]
  dsimp
  rw [hzero]
  have : N - x.val + 0 = N - x.val := by omega
  rw [this]
  have : N - x.val < N := by omega
  exact Nat.mod_eq_of_lt this

lemma circulant_mixed_graph_cycle_g_exists_arith_even
    (z n : ℕ) (hz : 1 ≤ z) (he : Even z) :
    let N := z * n + 2
    let m := N / 2
    let h := (z + 1) / 2
    h = z / 2 ∧
    1 ≤ h ∧
    N = 2 * m ∧
    m = n * h + 1 ∧
    N - n * h = m + 1 ∧
    m + 1 ≤ m + z / 2 ∧
    ∀ i < n + 1, i * h < N := by
  intro N m h
  obtain ⟨k, rfl⟩ := he
  have hk : 1 ≤ k := by omega
  have h_div : (k + k + 1) / 2 = k := by omega
  have hz_div : (k + k) / 2 = k := by omega
  have hN_eq : (k + k) * n + 2 = 2 * (n * k + 1) := by ring
  have hm_eq : ((k + k) * n + 2) / 2 = n * k + 1 := by
    rw [hN_eq, Nat.mul_div_right _ (by omega)]
  change (k + k + 1) / 2 = (k + k) / 2 ∧
    1 ≤ (k + k + 1) / 2 ∧
    (k + k) * n + 2 = 2 * (((k + k) * n + 2) / 2) ∧
    ((k + k) * n + 2) / 2 = n * ((k + k + 1) / 2) + 1 ∧
    (k + k) * n + 2 - n * ((k + k + 1) / 2) = ((k + k) * n + 2) / 2 + 1 ∧
    ((k + k) * n + 2) / 2 + 1 ≤ ((k + k) * n + 2) / 2 + (k + k) / 2 ∧
    ∀ i < n + 1, i * ((k + k + 1) / 2) < (k + k) * n + 2
  rw [h_div, hz_div, hm_eq]
  refine ⟨rfl, hk, by omega, by omega, by omega, by omega, ?_⟩
  intro i hi
  have : i ≤ n := by omega
  have : i * k ≤ n * k := Nat.mul_le_mul_right k this
  omega

lemma circulant_mixed_graph_cycle_g_exists_arith_odd
    (z n : ℕ) (hz : 1 ≤ z) (hn : 2 ≤ n) (he : ¬ Even z) :
    let N := (z + 1) * n
    let m := N / 2
    let h := (z + 1) / 2
    1 ≤ h ∧
    N = 2 * m ∧
    m = n * h ∧
    N - n * h = m ∧
    0 < m ∧
    ∀ i < n + 1, i * h < N := by
  intro N m h
  dsimp [N, m, h]
  obtain ⟨k, rfl⟩ : ∃ k, z = 2 * k + 1 := Nat.not_even_iff_odd.mp he
  have h_div : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have hN_eq : (2 * k + 1 + 1) * n = 2 * (n * (k + 1)) := by ring
  have hm_eq : ((2 * k + 1 + 1) * n) / 2 = n * (k + 1) := by
    rw [hN_eq, Nat.mul_div_right _ (by omega)]
  have h1 : 1 ≤ (2 * k + 1 + 1) / 2 := by rw [h_div]; omega
  have h2 : (2 * k + 1 + 1) * n = 2 * (((2 * k + 1 + 1) * n) / 2) := by rw [hm_eq]; ring
  have h3 : ((2 * k + 1 + 1) * n) / 2 = n * ((2 * k + 1 + 1) / 2) := by rw [hm_eq, h_div]
  have h4 : (2 * k + 1 + 1) * n - n * ((2 * k + 1 + 1) / 2) = ((2 * k + 1 + 1) * n) / 2 := by
    rw [hm_eq, h_div]; omega
  have h5 : 0 < ((2 * k + 1 + 1) * n) / 2 := by rw [hm_eq]; nlinarith
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro i hi
  rw [h_div]
  have : i ≤ n := by omega
  have : i * (k + 1) ≤ n * (k + 1) := Nat.mul_le_mul_right (k + 1) this
  have : n * (k + 1) < 2 * (n * (k + 1)) := by nlinarith
  linarith

/-- The circulant mixed graph M(z, g) contains a mixed cycle of length g. -/
theorem circulant_mixed_graph_cycle_g_exists (z g : ℕ) (hz : 1 ≤ z) (hg : 3 ≤ g) :
    let N := if Even z then z * (g - 1) + 2 else (z + 1) * (g - 1)
    let m := N / 2
    let E := SimpleGraph.fromRel fun (x y : Fin N) => (y - x).val = m
    let A : Fin N → Fin N → Prop := fun x y =>
      (1 ≤ (y - x).val ∧ (y - x).val ≤ (z + 1) / 2) ∨
      (m + 1 ≤ (y - x).val ∧ (y - x).val ≤ m + z / 2)
    mixed_graph_has_cycle E A g := by
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  intro N m E A
  have hg_le : 3 ≤ n + 1 := hg
  refine ⟨hg_le, ?_⟩
  have h_bound : ∀ i < n + 1, i * ((z + 1) / 2) < N := by
    intro i hi
    dsimp [N]
    split_ifs with he
    · exact (circulant_mixed_graph_cycle_g_exists_arith_even z n hz he).2.2.2.2.2.2 i hi
    · exact (circulant_mixed_graph_cycle_g_exists_arith_odd z n hz hn he).2.2.2.2.2 i hi
  let x : Fin (n + 1) → Fin N := fun i => ⟨i.val * ((z + 1) / 2), h_bound i.val i.isLt⟩
  refine ⟨x, ?_, ?_⟩
  · -- Injective
    intro i j hij
    simp only [x, Fin.mk.injEq] at hij
    have hpos : 0 < (z + 1) / 2 := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hpos hij)
  · -- Cycle condition
    intro i
    have hx_val : ∀ j : Fin (n + 1), (x j).val = j.val * ((z + 1) / 2) := fun _ => rfl
    by_cases hi : i = Fin.last n
    · -- hi : i = Fin.last n
      have hrot : finRotate (n + 1) i = 0 := by
        rw [hi, finRotate_last]
      have hi_val : i.val = n := by
        rw [hi]
        rfl
      have hrot_val : (x (finRotate (n + 1) i)).val = 0 := by
        rw [hrot, hx_val, Fin.val_zero, Nat.zero_mul]
      have hx_i_pos : 0 < (x i).val := by
        rw [hx_val, hi_val]
        have : 0 < (z + 1) / 2 := by omega
        nlinarith
      have hsub : (x (finRotate (n + 1) i) - x i).val = N - n * ((z + 1) / 2) := by
        have := circulant_mixed_graph_cycle_g_exists_sub_zero_eq (x i)
          (x (finRotate (n + 1) i)) hrot_val hx_i_pos
        rw [this, hx_val, hi_val]
      by_cases he : Even z
      · -- Even z
        obtain ⟨he1, he2, he3, he4, he5, he6, he7⟩ :=
          circulant_mixed_graph_cycle_g_exists_arith_even z n hz he
        have hN_eq : N = z * n + 2 := by dsimp [N]; rw [if_pos he]
        have hm_eq : m = (z * n + 2) / 2 := by dsimp [m]; rw [hN_eq]
        have hsub' : (x (finRotate (n + 1) i) - x i).val = m + 1 := by
          rw [hsub, hN_eq, he5, ← hm_eq]
        right
        right
        rw [hsub', hm_eq]
        exact ⟨le_rfl, he6⟩
      · -- Odd z
        obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6⟩ :=
          circulant_mixed_graph_cycle_g_exists_arith_odd z n hz hn he
        have hN_eq : N = (z + 1) * n := by dsimp [N]; rw [if_neg he]
        have hm_eq : m = ((z + 1) * n) / 2 := by dsimp [m]; rw [hN_eq]
        have hsub' : (x (finRotate (n + 1) i) - x i).val = m := by
          rw [hsub, hN_eq, ho4, ← hm_eq]
        left
        rw [SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inl hsub'⟩
        intro h_eq
        have : (x i).val = (x (finRotate (n + 1) i)).val := congrArg Fin.val h_eq
        rw [hx_val, hi_val, hrot_val] at this
        have : 0 < n * ((z + 1) / 2) := by
          have : 0 < n := by omega
          have : 0 < (z + 1) / 2 := by omega
          positivity
        omega
    · -- hi : i ≠ Fin.last n
      have hrot : (finRotate (n + 1) i).val = i.val + 1 := coe_finRotate_of_ne_last hi
      have hsub : (x (finRotate (n + 1) i) - x i).val = (z + 1) / 2 := by
        have hy_eq : (x (finRotate (n + 1) i)).val = (x i).val + (z + 1) / 2 := by
          rw [hx_val, hx_val, hrot]
          ring
        have hN_lt : (x i).val + (z + 1) / 2 < N := by
          rw [← hy_eq]
          exact (x (finRotate (n + 1) i)).isLt
        exact circulant_mixed_graph_cycle_g_exists_sub_eq_of_add_eq (x i)
          (x (finRotate (n + 1) i)) ((z + 1) / 2) hy_eq hN_lt
      right
      left
      rw [hsub]
      have : 1 ≤ (z + 1) / 2 := by omega
      exact ⟨this, le_rfl⟩
