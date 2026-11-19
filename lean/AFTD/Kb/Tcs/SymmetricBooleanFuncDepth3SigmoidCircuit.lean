import AFTD.Prelude
import AFTD.Kb.Tcs.Depth3SigmoidCircuit
import AFTD.Kb.Tcs.HammingWeight
import AFTD.Kb.Tcs.IsSymmetricBooleanFunc
import AFTD.Kb.Tcs.Depth3SigmoidCircuitEval
import AFTD.Kb.Tcs.Depth3SigmoidCircuitEvalBool
import AFTD.Kb.Tcs.Depth3SigmoidCircuitNumWires
import AFTD.Kb.Tcs.Depth3SigmoidCircuitWeightsBoundedBy
import AFTD.Kb.Tcs.SigmoidSubGeOfLe
import AFTD.Kb.Tcs.SigmoidLayer3SeparationHigh
import AFTD.Kb.Tcs.SigmoidLayer3SeparationLow
import AFTD.Kb.Tcs.Bit

/-!
# symmetric_boolean_func_depth3_sigmoid_circuit

Topic: circuits   Node: c92da435df31

Provenance: formalization of a published result. Source: scout/2611-21910-new-gate-weight-and-wire-complexity-bounds-for-sigmoid-neur.md:893

For every symmetric Boolean function f on n ≥ 1 variables, there exists a depth-3 sigmoidal circuit C on n inputs with at most 3n wires and all weights and biases bounded by 12n * ln(10n) + 1 that computes f with separation at least 1/4: the output is strictly greater than 3/4 whenever f(x) = true, and strictly less than 1/4 whenever f(x) = false.
-/

open Real

lemma sbfd3_hw_sum {n : ℕ} (x : Fin n → Bool) :
    ∑ i : Fin n, bit (x i) = (hamming_weight x : ℝ) := by
  simp only [bit, hamming_weight]
  rw [Finset.sum_boole]

lemma sbfd3_hw_le_nat {n : ℕ} (x : Fin n → Bool) : hamming_weight x ≤ n := by
  rw [hamming_weight]
  calc ({i : Fin n | x i = true} : Finset (Fin n)).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

lemma sbfd3_telescoping_ind (g : ℕ → ℝ) (hw n : ℕ) (hwn : hw ≤ n) :
    ∑ k ∈ Finset.range n, (g (k+1) - g k) * (if k < hw then (1:ℝ) else 0) = g hw - g 0 := by
  have hsub : Finset.range hw ⊆ Finset.range n := Finset.range_subset_range.mpr hwn
  have hz : ∀ x ∈ Finset.range n, x ∉ Finset.range hw →
      (g (x+1) - g x) * (if x < hw then (1:ℝ) else 0) = 0 := by
    intro x hx hxnot
    rw [Finset.mem_range] at hxnot
    have : ¬ x < hw := by omega
    rw [if_neg this, mul_zero]
  rw [← Finset.sum_subset hsub hz]
  rw [Finset.sum_congr rfl ?_, Finset.sum_range_sub]
  intro k hk
  rw [if_pos (Finset.mem_range.mp hk), mul_one]

lemma sbfd3_sig_ge_log (y c : ℝ) (hc : 0 < c) (h : Real.log c ≤ y) : 1 - 1/c ≤ Real.sigmoid y := by
  have hr : Real.exp (-Real.log c) = 1/c := by rw [Real.exp_neg, Real.exp_log hc, inv_eq_one_div]
  have he : Real.exp (-y) ≤ 1/c := by rw [← hr]; exact Real.exp_le_exp.mpr (by linarith)
  have ht1 : 1 - Real.exp (-y) ≤ Real.sigmoid y := by
    rw [Real.sigmoid_def, ← one_div, le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (Real.exp (-y))]
  linarith

lemma sbfd3_sig_le_neg_log (y c : ℝ) (hc : 0 < c) (hc1 : 1 ≤ c) (h : y ≤ -Real.log c) : Real.sigmoid y ≤ 1/c := by
  have hr : Real.exp (-Real.log c) = 1/c := by rw [Real.exp_neg, Real.exp_log hc, inv_eq_one_div]
  have he : Real.exp y ≤ 1/c := by rw [← hr]; exact Real.exp_le_exp.mpr h
  have hlog : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hy : y ≤ 0 := by linarith
  have ht2 : Real.sigmoid y ≤ Real.exp y := by
    rw [Real.sigmoid_def, ← one_div, div_le_iff₀ (by positivity)]
    have h : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos y]
  linarith

lemma sbfd3_log10_ge_one : (1:ℝ) ≤ Real.log 10 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  linarith [Real.exp_one_lt_three]

lemma sbfd3_per_term_bound
    (n : ℕ) (hn : 1 ≤ n) (A : ℝ)
    (hA : 12 * (n:ℝ) * Real.log (10 * (n:ℝ)) ≤ A)
    (w : ℕ) (hw : w ≤ n) (k : Fin n) :
    |Real.sigmoid (A * (Real.sigmoid ((w:ℝ)/(n:ℝ)) - Real.sigmoid ((((k:ℝ) + 1/2)/(n:ℝ)))))
       - (if (k:ℕ) < w then (1:ℝ) else 0)| ≤ 1/(10*(n:ℝ)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log (10*(n:ℝ)) := by
    apply Real.log_pos; nlinarith
  have hA0 : 0 ≤ A := by nlinarith
  have hwR1 : (w:ℝ) ≤ n := by exact_mod_cast hw
  have hklt : (k:ℝ) < n := by exact_mod_cast k.isLt
  have hk1 : (k:ℝ) + 1 ≤ n := by
    have : (k:ℕ) + 1 ≤ n := k.isLt
    exact_mod_cast this
  have ht0 : 0 ≤ ((k:ℝ) + 1/2)/(n:ℝ) := by positivity
  have ht1 : ((k:ℝ) + 1/2)/(n:ℝ) ≤ 1 := by
    rw [div_le_iff₀ hn0]; nlinarith [hk1]
  have hwn0 : 0 ≤ (w:ℝ)/n := by positivity
  have hwn1 : (w:ℝ)/n ≤ 1 := by rw [div_le_iff₀ hn0]; linarith
  by_cases hcase : (k:ℕ) < w
  · rw [if_pos hcase]
    have hwge : (k:ℝ) + 1 ≤ (w:ℝ) := by
      have : (k:ℕ) + 1 ≤ w := by omega
      exact_mod_cast this
    have hle : ((k:ℝ)+1/2)/n ≤ (w:ℝ)/n := by
      rw [div_le_div_iff_of_pos_right hn0]; linarith
    have hwnt : (1:ℝ)/(2*n) ≤ (w:ℝ)/n - ((k:ℝ)+1/2)/n := by
      have heq1 : (w:ℝ)/n - ((k:ℝ)+1/2)/n = (w - (k+1/2))/n := by rw [div_sub_div_same]
      rw [heq1, show (1:ℝ)/(2*n) = ((1:ℝ)/2)/n by field_simp]
      rw [div_le_div_iff_of_pos_right hn0]; linarith
    have hpos : (1:ℝ)/(12*n) ≤ Real.sigmoid ((w:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n) := by
      have hmono := sigmoid_sub_ge_of_le (((k:ℝ)+1/2)/n) ((w:ℝ)/n) ht0 hle hwn1
      have h12 : (1:ℝ)/(12*n) = (1/6) * ((1:ℝ)/(2*n)) := by field_simp; norm_num
      rw [h12]
      calc (1/6) * (1/(2*n)) ≤ (1/6) * ((w:ℝ)/n - ((k:ℝ)+1/2)/n) := by
              apply mul_le_mul_of_nonneg_left hwnt; norm_num
        _ ≤ Real.sigmoid ((w:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n) := hmono
    have harg_ge : Real.log (10*n) ≤ A * (Real.sigmoid ((w:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n)) := by
      have h1 : A * ((1:ℝ)/(12*n)) ≤ A * (Real.sigmoid ((w:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n)) :=
        mul_le_mul_of_nonneg_left hpos hA0
      have h2 : Real.log (10*n) ≤ A * ((1:ℝ)/(12*n)) := by
        rw [show A * ((1:ℝ)/(12*n)) = A/(12*n) by ring, le_div_iff₀ (by positivity)]
        nlinarith [hA]
      linarith
    have hV_ge : 1 - 1/(10*n) ≤ Real.sigmoid (A * (Real.sigmoid ((w:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n))) :=
      sbfd3_sig_ge_log _ (10*(n:ℝ)) (by positivity) harg_ge
    have hV_le : Real.sigmoid (A * (Real.sigmoid ((w:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n))) ≤ 1 :=
      Real.sigmoid_le_one _
    rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [if_neg hcase]
    have hwle : (w:ℝ) ≤ (k:ℝ) := by
      have : w ≤ (k:ℕ) := by omega
      exact_mod_cast this
    have hle : (w:ℝ)/n ≤ ((k:ℝ)+1/2)/n := by
      rw [div_le_div_iff_of_pos_right hn0]; linarith
    have hwnt : (1:ℝ)/(2*n) ≤ ((k:ℝ)+1/2)/n - (w:ℝ)/n := by
      have heq1 : ((k:ℝ)+1/2)/n - (w:ℝ)/n = (k+1/2 - w)/n := by rw [div_sub_div_same]
      rw [heq1, show (1:ℝ)/(2*n) = ((1:ℝ)/2)/n by field_simp]
      rw [div_le_div_iff_of_pos_right hn0]; linarith
    have hpos : (1:ℝ)/(12*n) ≤ Real.sigmoid (((k:ℝ)+1/2)/n) - Real.sigmoid ((w:ℝ)/n) := by
      have hmono := sigmoid_sub_ge_of_le ((w:ℝ)/n) (((k:ℝ)+1/2)/n) hwn0 hle ht1
      have h12 : (1:ℝ)/(12*n) = (1/6) * ((1:ℝ)/(2*n)) := by field_simp; norm_num
      rw [h12]
      calc (1/6) * (1/(2*n)) ≤ (1/6) * (((k:ℝ)+1/2)/n - (w:ℝ)/n) := by
              apply mul_le_mul_of_nonneg_left hwnt; norm_num
        _ ≤ Real.sigmoid (((k:ℝ)+1/2)/n) - Real.sigmoid ((w:ℝ)/n) := hmono
    have harg_le : A * (Real.sigmoid ((w:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n)) ≤ -Real.log (10*n) := by
      have h1 : A * (Real.sigmoid ((w:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n))
          = -(A * (Real.sigmoid (((k:ℝ)+1/2)/n) - Real.sigmoid ((w:ℝ)/n))) := by ring
      rw [h1]
      have h2 : A * ((1:ℝ)/(12*n)) ≤ A * (Real.sigmoid (((k:ℝ)+1/2)/n) - Real.sigmoid ((w:ℝ)/n)) :=
        mul_le_mul_of_nonneg_left hpos hA0
      have h3 : Real.log (10*n) ≤ A * ((1:ℝ)/(12*n)) := by
        rw [show A * ((1:ℝ)/(12*n)) = A/(12*n) by ring, le_div_iff₀ (by positivity)]
        nlinarith [hA]
      linarith
    have hV_le : Real.sigmoid (A * (Real.sigmoid ((w:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n))) ≤ 1/(10*n) :=
      sbfd3_sig_le_neg_log _ (10*(n:ℝ)) (by positivity) (by nlinarith) harg_le
    have hV_ge : 0 ≤ Real.sigmoid (A * (Real.sigmoid ((w:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n))) :=
      Real.sigmoid_nonneg _
    rw [abs_of_nonneg (by linarith), sub_zero]
    exact hV_le

/-- Linear wire upper bound for symmetric Boolean functions in depth-3 sigmoidal circuits (Theorem 4.1). -/
theorem symmetric_boolean_func_depth3_sigmoid_circuit
    (n : ℕ) (hn : 1 ≤ n) (f : (Fin n → Bool) → Bool) (hf : is_symmetric_boolean_func f) :
    ∃ C : Depth3SigmoidCircuit n,
      depth3_sigmoid_circuit_num_wires C ≤ 3 * n ∧
      depth3_sigmoid_circuit_weights_bounded_by C (12 * (n : ℝ) * Real.log (10 * (n : ℝ)) + 1) ∧
      (∀ x : Fin n → Bool, f x = true → 3 / 4 < depth3_sigmoid_circuit_eval_bool C x) ∧
      (∀ x : Fin n → Bool, f x = false → depth3_sigmoid_circuit_eval_bool C x < 1 / 4) := by
  obtain ⟨F, hF⟩ := hf
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  let A : ℝ := (Nat.ceil (12 * (n:ℝ) * Real.log (10*(n:ℝ))))
  let g : ℕ → ℝ := fun m => if F m = true then 1 else 0
  let cc : Fin n → ℝ := fun k => g ((k:ℕ)+1) - g (k:ℕ)
  let B : ℝ := 12 * (n:ℝ) * Real.log (10*(n:ℝ)) + 1
  let C : Depth3SigmoidCircuit n :=
    { m₁ := 1, m₂ := n, w₁ := fun _ _ => (1:ℝ)/n, b₁ := fun _ => 0,
      w₂ := fun _ _ => A, b₂ := fun k => -A * Real.sigmoid ((((k:ℝ) + 1/2)/(n:ℝ))),
      w₃ := fun k => 4 * cc k, b₃ := 4 * (g 0 - 1/2) }
  have hlog : 0 < Real.log (10*(n:ℝ)) := by apply Real.log_pos; nlinarith
  have hAle_ceil : 12 * (n:ℝ) * Real.log (10*(n:ℝ)) ≤ A := Nat.le_ceil _
  have hApos : 0 < A := by
    have h0 : 0 < 12 * (n:ℝ) * Real.log (10*(n:ℝ)) := by positivity
    have hc : 0 < Nat.ceil (12 * (n:ℝ) * Real.log (10*(n:ℝ))) := Nat.ceil_pos.mpr h0
    simp only [A]; exact_mod_cast hc
  have hA0 : 0 ≤ A := le_of_lt hApos
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hAle : A ≤ B := by
    have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 12 * (n:ℝ) * Real.log (10*(n:ℝ)) by positivity)
    simp only [B]; linarith
  have hB4 : (4:ℝ) ≤ B := by
    have h10 : 1 ≤ Real.log 10 := sbfd3_log10_ge_one
    have hln : Real.log (10*(n:ℝ)) = Real.log 10 + Real.log (n:ℝ) :=
      Real.log_mul (by norm_num) (by positivity)
    have hln0 : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
    simp only [B, hln]; nlinarith
  have hw1pos : (0:ℝ) < 1/n := by positivity
  have hw1ne : (1:ℝ)/n ≠ 0 := ne_of_gt hw1pos
  have hw1le : (1:ℝ)/n ≤ 1 := by
    rw [div_le_one hn0]; exact hn1
  have hg01 : g 0 ≤ 1 := by simp only [g]; split <;> norm_num
  have hg00 : 0 ≤ g 0 := by simp only [g]; split <;> norm_num
  have hccb : ∀ k : Fin n, |g ((k:ℕ)+1) - g (k:ℕ)| ≤ 1 := by
    intro k
    have ha : 0 ≤ g ((k:ℕ)+1) := by simp only [g]; split <;> norm_num
    have hb : g ((k:ℕ)+1) ≤ 1 := by simp only [g]; split <;> norm_num
    have hc : 0 ≤ g (k:ℕ) := by simp only [g]; split <;> norm_num
    have hd : g (k:ℕ) ≤ 1 := by simp only [g]; split <;> norm_num
    rw [abs_le]; constructor <;> linarith
  have heval : ∀ x : Fin n → Bool,
      depth3_sigmoid_circuit_eval_bool C x
        = Real.sigmoid (4 * (g 0 + ∑ k : Fin n, cc k * Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n))) - 1/2)) := by
    intro x
    simp only [depth3_sigmoid_circuit_eval_bool, depth3_sigmoid_circuit_eval, C]
    have hL1 : (∑ i : Fin n, (1:ℝ)/n * (if x i = true then 1 else 0) + 0)
        = (hamming_weight x : ℝ)/n := by
      rw [add_zero, ← Finset.mul_sum]
      have hb : (∑ i : Fin n, (if x i = true then (1:ℝ) else 0)) = (hamming_weight x : ℝ) := by
        simpa only [bit] using sbfd3_hw_sum x
      rw [hb]; ring
    simp only [hL1, Fin.sum_univ_one]
    have hlin : ∀ (X Y : ℝ), A * X + -A * Y = A * (X - Y) := by intro X Y; ring
    simp only [hlin]
    have hsum : (∑ x_1 : Fin n, 4 * cc x_1 * (A * ((Real.sigmoid ((hamming_weight x : ℝ) / (n : ℝ))) - Real.sigmoid (((x_1:ℝ)+1/2)/n))).sigmoid)
         = 4 * (∑ x_1 : Fin n, cc x_1 * (A * ((Real.sigmoid ((hamming_weight x : ℝ) / (n : ℝ))) - Real.sigmoid (((x_1:ℝ)+1/2)/n))).sigmoid) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    ring
  have hsep : ∀ x : Fin n → Bool,
      |(g 0 + ∑ k : Fin n, cc k * Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n)))) - g (hamming_weight x)| ≤ 1/10 := by
    intro x
    have hV : ∀ k : Fin n, |Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/(n:ℝ)) - Real.sigmoid (((k:ℝ)+1/2)/n))) - (if (k:ℕ) < hamming_weight x then (1:ℝ) else 0)| ≤ 1/(10*(n:ℝ)) :=
      fun k => sbfd3_per_term_bound n hn A hAle_ceil (hamming_weight x) (sbfd3_hw_le_nat x) k
    have hsum : |∑ k : Fin n, cc k * Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/(n:ℝ)) - Real.sigmoid (((k:ℝ)+1/2)/n))) - (g (hamming_weight x) - g 0)| ≤ 1/10 := by
      have hind : (∑ k : Fin n, cc k * (if (k:ℕ) < hamming_weight x then (1:ℝ) else 0)) = g (hamming_weight x) - g 0 := by
        simp only [cc]
        rw [Fin.sum_univ_eq_sum_range (fun k => (g (k+1) - g k) * (if k < hamming_weight x then (1:ℝ) else 0)) n]
        exact sbfd3_telescoping_ind g (hamming_weight x) n (sbfd3_hw_le_nat x)
      rw [← hind, ← Finset.sum_sub_distrib]
      calc |∑ k : Fin n, (cc k * Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/(n:ℝ)) - Real.sigmoid (((k:ℝ)+1/2)/n))) - cc k * (if (k:ℕ) < hamming_weight x then (1:ℝ) else 0))|
          ≤ ∑ k : Fin n, |cc k * Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/(n:ℝ)) - Real.sigmoid (((k:ℝ)+1/2)/n))) - cc k * (if (k:ℕ) < hamming_weight x then (1:ℝ) else 0)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin n, (1/(10*(n:ℝ))) := by
            apply Finset.sum_le_sum
            intro k _
            have h1 : cc k * Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/(n:ℝ)) - Real.sigmoid (((k:ℝ)+1/2)/n))) - cc k * (if (k:ℕ) < hamming_weight x then (1:ℝ) else 0)
                = cc k * (Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/(n:ℝ)) - Real.sigmoid (((k:ℝ)+1/2)/n))) - (if (k:ℕ) < hamming_weight x then (1:ℝ) else 0)) := by ring
            rw [h1, abs_mul]
            calc |cc k| * |Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/(n:ℝ)) - Real.sigmoid (((k:ℝ)+1/2)/n))) - (if (k:ℕ) < hamming_weight x then (1:ℝ) else 0)|
                ≤ 1 * (1/(10*(n:ℝ))) :=
                  mul_le_mul (hccb k) (hV k) (abs_nonneg _) (by norm_num)
              _ = 1/(10*(n:ℝ)) := one_mul _
        _ = 1/10 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp only [nsmul_eq_mul]
            field_simp
    calc |(g 0 + ∑ k : Fin n, cc k * Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n)))) - g (hamming_weight x)|
        = |(∑ k : Fin n, cc k * Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n)))) - (g (hamming_weight x) - g 0)| := by
          congr 1; ring
      _ ≤ 1/10 := hsum
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · unfold depth3_sigmoid_circuit_num_wires
    simp only [C]
    have h3 : ({x : Fin n | 4 * cc x ≠ 0} : Finset (Fin n)).card ≤ n := by
      calc ({x : Fin n | 4 * cc x ≠ 0} : Finset (Fin n)).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
        _ = n := by simp
    have e1 : (∑ x : Fin 1, ({x : Fin n | (1:ℝ)/n ≠ 0} : Finset (Fin n)).card) = n := by
      have h : ∀ j : Fin 1, ({i : Fin n | (1:ℝ)/n ≠ 0} : Finset (Fin n)).card = n := by
        intro j; rw [Finset.filter_true_of_mem (fun i _ => hw1ne)]; simp
      rw [Finset.sum_congr rfl (fun i _ => h i)]; simp
    have e2 : (∑ x : Fin n, ({x : Fin 1 | A ≠ 0} : Finset (Fin 1)).card) = n := by
      have h : ∀ k : Fin n, ({j : Fin 1 | A ≠ 0} : Finset (Fin 1)).card = 1 := by
        intro k; rw [Finset.filter_true_of_mem (fun j _ => hAne)]; simp
      rw [Finset.sum_congr rfl (fun i _ => h i)]; simp
    rw [e1, e2]; omega
  · unfold depth3_sigmoid_circuit_weights_bounded_by
    simp only [C]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j i
      have h1 : |(1:ℝ)/n| = 1/n := abs_of_pos hw1pos
      rw [h1]
      linarith
    · intro j; simp only [abs_zero]; linarith
    · intro k j; rw [abs_of_nonneg hA0]; exact hAle
    · intro k
      rw [abs_mul, abs_neg]
      have h1 : |A| = A := abs_of_nonneg hA0
      have h2 : |Real.sigmoid ((((k:ℝ) + 1/2)/(n:ℝ)))| ≤ 1 := by
        rw [abs_of_pos (Real.sigmoid_pos _)]
        exact Real.sigmoid_le_one _
      rw [h1]
      calc A * |Real.sigmoid ((((k:ℝ) + 1/2)/(n:ℝ)))| ≤ A * 1 :=
              mul_le_mul_of_nonneg_left h2 hA0
        _ = A := mul_one A
        _ ≤ B := hAle
    · intro k
      rw [abs_mul]
      have h4 : |(4:ℝ)| = 4 := by norm_num
      rw [h4]
      calc 4 * |cc k| ≤ 4 * 1 := mul_le_mul_of_nonneg_left (hccb k) (by norm_num)
        _ ≤ B := by linarith
    · rw [abs_le]; constructor <;> linarith
  · intro x hx
    have hFx : F (hamming_weight x) = true := by
      have h := hF x; rw [hx] at h; exact h.symm
    have hghw : g (hamming_weight x) = 1 := by simp only [g]; rw [hFx]; norm_num
    have hbd := hsep x
    rw [hghw] at hbd
    have hL : (9:ℝ)/10 ≤ g 0 + ∑ k : Fin n, cc k * Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n))) := by
      rw [abs_le] at hbd; linarith [hbd.1]
    rw [heval x]
    exact sigmoid_layer3_separation_high _ hL
  · intro x hx
    have hFx : F (hamming_weight x) = false := by
      have h := hF x; rw [hx] at h; exact h.symm
    have hghw : g (hamming_weight x) = 0 := by simp only [g]; rw [hFx]; norm_num
    have hbd := hsep x
    rw [hghw] at hbd
    have hL : g 0 + ∑ k : Fin n, cc k * Real.sigmoid (A * (Real.sigmoid ((hamming_weight x:ℝ)/n) - Real.sigmoid (((k:ℝ)+1/2)/n))) ≤ 1/10 := by
      rw [abs_le] at hbd; linarith [hbd.2]
    rw [heval x]
    exact sigmoid_layer3_separation_low _ hL
