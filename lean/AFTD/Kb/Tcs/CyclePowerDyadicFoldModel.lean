import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_fold_model

Topic: combinatorics   Node: 34a40f8efffa

Provenance: helper lemma. RT-1 / OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Session 2026-11-09: folding offsets modulo 2^t (experiment 19407).

The fold of a tight dyadic class model. If x is a tight, exactly dyadically covered, fully covered integer Boolean class model at exponent t+1 (t ≥ 1) with t+2 active classes per vertex, and the left count A(v) = Σ_{a<2^t} x(v-a, a) is 2^t-periodic, then the fold y(p, a) = x(p, a) or x(p, a+2^t) is such a model at exponent t with t+1 active classes per vertex.
-/

theorem cycle_power_dyadic_fold_parents (t : ℕ) (ht : 1 ≤ t) (b : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight (t+1) b =
      (Finset.range (2^(t+1))).sum (fun a => (b a).toNat)) :
    (∀ a, a < 2^(t-1) → b (a + 2^t) = true → b a = true) ∧
    (∀ a, 2^(t-1) ≤ a → a < 2^t → b a = true → b (a + 2^t) = true) := by
  have P := cycle_power_dyadic_tight_class_parent (t+1) t ht (by omega) b htight
  have e : ∀ a : ℕ, a + 2^(t+1) - 2^t = a + 2^t := by
    intro a; rw [pow_succ]; omega
  have hle : (2:ℕ)^(t-1) ≤ 2^t := Nat.pow_le_pow_right (by norm_num) (by omega)
  constructor
  · intro a ha h
    exact (P a (lt_of_lt_of_le ha hle)).1 ha (by rw [e]; exact h)
  · intro a ha hlt h
    have := (P a hlt).2 ha h
    rwa [e] at this

theorem cycle_power_dyadic_fold_pair (t : ℕ) (ht : 1 ≤ t) (b : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight (t+1) b =
      (Finset.range (2^(t+1))).sum (fun a => (b a).toNat))
    (j i : ℕ) (hj : j < t) (hi : i < 2^j) :
    ((b i || b (i + 2^t)) && (b (i + 2^t - 2^j) || b (i + 2^t - 2^j + 2^t))) =
      (b i && b (i + 2^(t+1) - 2^j)) := by
  obtain ⟨P1, P2⟩ := cycle_power_dyadic_fold_parents t ht b htight
  have hQ : (2:ℕ)^j ≤ 2^(t-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2t : (2:ℕ)^t = 2 * 2^(t-1) := by
    rw [← pow_succ']; congr 1; omega
  have hs : (2:ℕ)^(t+1) = 2 * 2^t := by rw [pow_succ']
  have hc1 : 2^(t-1) ≤ i + 2^t - 2^j := by omega
  have hc2 : i + 2^t - 2^j < 2^t := by omega
  have hc3 : i + 2^t - 2^j + 2^t = i + 2^(t+1) - 2^j := by omega
  have h1 : b (i + 2^t) = true → b i = true := P1 i (by omega)
  have h2 : b (i + 2^t - 2^j) = true → b (i + 2^t - 2^j + 2^t) = true := P2 _ hc1 hc2
  rw [← hc3]
  generalize b (i + 2^t - 2^j + 2^t) = w at *
  generalize b (i + 2^t - 2^j) = u at *
  generalize b (i + 2^t) = y at *
  generalize b i = z at *
  cases z <;> cases y <;> cases u <;> cases w <;> simp_all

theorem cycle_power_dyadic_fold_tight (t : ℕ) (ht : 1 ≤ t) (b : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight (t+1) b =
      (Finset.range (2^(t+1))).sum (fun a => (b a).toNat)) :
    cycle_power_dyadic_class_weight t (fun a => b a || b (a + 2^t)) =
      (Finset.range (2^t)).sum (fun a => (b a || b (a + 2^t)).toNat) := by
  have hpair := cycle_power_dyadic_fold_pair t ht b htight
  have hsize : (Finset.range (2^(t+1))).sum (fun a => (b a).toNat) =
      (Finset.range (2^t)).sum (fun a => (b a || b (a + 2^t)).toNat) +
      (Finset.range (2^t)).sum (fun a => (b a && b (a + 2^t)).toNat) := by
    rw [pow_succ, mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.add_comm (2^t) a]
    cases b a <;> cases b (a + 2^t) <;> rfl
  have h0 := hpair 0 0 (by omega) (by norm_num)
  simp only [Nat.zero_add, pow_zero] at h0
  have htop : (if t = 0 then 0 else (Finset.range (2^t)).sum
      (fun i => (b i && b (i + 2^(t+1) - 2^t)).toNat)) =
      (Finset.range (2^t)).sum (fun a => (b a && b (a + 2^t)).toNat) := by
    rw [if_neg (by omega)]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : a + 2^(t+1) - 2^t = a + 2^t := by rw [pow_succ]; omega
    rw [this]
  have hrest : (Finset.range t).sum (fun j => if j = 0 then 0 else
      (Finset.range (2^j)).sum (fun i =>
        ((b i || b (i + 2^t)) && (b (i + 2^t - 2^j) || b (i + 2^t - 2^j + 2^t))).toNat)) =
      (Finset.range t).sum (fun j => if j = 0 then 0 else
      (Finset.range (2^j)).sum (fun i => (b i && b (i + 2^(t+1) - 2^j)).toNat)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    split_ifs
    · rfl
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [hpair j i (Finset.mem_range.mp hj) (Finset.mem_range.mp hi)]
  unfold cycle_power_dyadic_class_weight at htight ⊢
  rw [Finset.sum_range_succ, htop, hsize] at htight
  simp only []
  rw [hrest, show (0 + 2^t : ℕ) = 2^t from Nat.zero_add _, h0]
  omega

theorem cycle_power_dyadic_fold_model (t : ℕ) (ht : 1 ≤ t) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (t+1) (x p) =
      (Finset.range (2^(t+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < t+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(t+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(t+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (t+1)+1)
    (hfold : ∀ v : ℤ, (Finset.range (2^t)).sum (fun a => (x (v-(a : ℤ)) a).toNat) =
      (Finset.range (2^t)).sum (fun a => (x (v+(2:ℤ)^t-(a : ℤ)) a).toNat)) :
    let y : ℤ → ℕ → Bool := fun p a => x p a || x p (a + 2^t)
    (∀ p, cycle_power_dyadic_class_weight t (y p) =
      (Finset.range (2^t)).sum (fun a => (y p a).toNat)) ∧
    (∀ j < t, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^t-2^j)).toNat) = 1) ∧
    (∀ d : ℕ, 1 ≤ d → d < 2^t → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^t-d ∧ y (v-(a : ℤ)) a = true ∧
        y (v-(a : ℤ)) (a+d) = true) ∧
    (∀ v : ℤ, (Finset.range (2^t)).sum (fun a =>
      (y (v-(a : ℤ)) a).toNat) = t+1) := by
  intro y
  have hs : (2:ℕ)^(t+1) = 2^t + 2^t := by rw [pow_succ, mul_two]
  refine ⟨fun p => cycle_power_dyadic_fold_tight t ht (x p) (htight p), ?_, ?_, ?_⟩
  · intro j hj v
    rw [← hexact j (by omega) v]
    refine Finset.sum_congr rfl fun a ha => ?_
    show (((x (v-(a:ℤ)) a || x (v-(a:ℤ)) (a+2^t)) &&
      (x (v-(a:ℤ)) (a+2^t-2^j) || x (v-(a:ℤ)) (a+2^t-2^j+2^t))).toNat) = _
    rw [cycle_power_dyadic_fold_pair t ht (x (v-(a:ℤ))) (htight _) j a hj (Finset.mem_range.mp ha)]
  · intro d hd1 hd2 v
    obtain ⟨a, ha, h1, h2⟩ := hcover (d + 2^t) (by omega) (by omega) v
    refine ⟨a, by omega, ?_, ?_⟩
    · simp [y, h1]
    · have e : a + (d + 2^t) = a + d + 2^t := by ring
      rw [e] at h2
      simp [y, h2]
  · intro v
    have hP : (Finset.range (2^t)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^t)).toNat) = 1 := by
      rw [← hexact t (by omega) v]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : a + 2^(t+1) - 2^t = a + 2^t := by rw [pow_succ]; omega
      rw [this]
    have hC := hcount (v + (2:ℤ)^t)
    rw [hs, Finset.sum_range_add] at hC
    have hB : (Finset.range (2^t)).sum (fun i =>
        (x (v + (2:ℤ)^t - ((2^t + i : ℕ) : ℤ)) (2^t + i)).toNat) =
        (Finset.range (2^t)).sum (fun a => (x (v-(a : ℤ)) (a+2^t)).toNat) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have e1 : v + (2:ℤ)^t - ((2^t + i : ℕ) : ℤ) = v - (i : ℤ) := by push_cast; ring
      rw [e1, Nat.add_comm (2^t) i]
    rw [hB, ← hfold v] at hC
    have hF : (Finset.range (2^t)).sum (fun a => (y (v-(a : ℤ)) a).toNat) +
        (Finset.range (2^t)).sum (fun a =>
          (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^t)).toNat) =
        (Finset.range (2^t)).sum (fun a => (x (v-(a : ℤ)) a).toNat) +
        (Finset.range (2^t)).sum (fun a => (x (v-(a : ℤ)) (a+2^t)).toNat) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      show (x (v-(a:ℤ)) a || x (v-(a:ℤ)) (a+2^t)).toNat + _ = _
      cases x (v-(a:ℤ)) a <;> cases x (v-(a:ℤ)) (a+2^t) <;> rfl
    omega
