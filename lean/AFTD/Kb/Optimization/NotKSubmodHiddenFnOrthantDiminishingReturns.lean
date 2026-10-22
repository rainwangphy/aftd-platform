import AFTD.Prelude
import AFTD.Kb.Optimization.IsKSubmodKernel
import AFTD.Kb.Optimization.KSubmodHiddenFn
import AFTD.Kb.Optimization.HasOrthantDiminishingReturns
import AFTD.Kb.Optimization.KSubmodLe

/-!
# not_k_submod_hidden_fn_orthant_diminishing_returns

Topic: submodular   Node: 4baf11117dc2

Provenance: original. Related work: refutes `k_submod_hidden_fn_orthant_diminishing_returns`

The statement `k_submod_hidden_fn_orthant_diminishing_returns` is false: The definition `is_k_submod_kernel` lacks differentiability/continuity hypotheses on H. In Lean, `deriv f x` evaluates to 0 when f is not differentiable at x. Consequently, discontinuous functions like H(x, y) = if x ≥ 1 then 1 else 0 satisfy `is_k_submod_kernel H` because their derivatives vanish identically on [0, 1]², satisfying conditions 6 and 7 vacuously. For this kernel, with n = 2, k = 2, σ ≡ 0, x = (none, none), y = (some 0, none), e = 1, and i = 0: we have x ≤ y and y 1 = none, but f(y + 0 1_1) - f(y) = 1 - 0 = 1 while f(x + 0 1_1) - f(x) = 0 - 0 = 0, contradicting orthant diminishing returns (1 ≤ 0 is false).
-/

theorem not_k_submod_hidden_fn_orthant_diminishing_returns : ¬ (∀ {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (σ : Fin n → Fin k)
    (H : ℝ → ℝ → ℝ) (hH : is_k_submod_kernel H), has_orthant_diminishing_returns (k_submod_hidden_fn H σ)) := by
  let H_counter : ℝ → ℝ → ℝ := fun x _ => if x ≥ 1 then 1 else 0
  have H_counter_not_diff : ∀ y : ℝ, ¬ DifferentiableAt ℝ (fun t => H_counter t y) 1 := by
    intro y h
    have hc : ContinuousAt (fun t => H_counter t y) 1 := h.continuousAt
    have hlim : Filter.Tendsto (fun t => H_counter t y) (nhdsWithin 1 (Set.Iio 1)) (nhds (H_counter 1 y)) :=
      hc.tendsto.mono_left inf_le_left
    have h0 : (fun t => H_counter t y) =ᶠ[nhdsWithin 1 (Set.Iio 1)] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have : ¬ (t ≥ 1) := not_le_of_gt ht
      simp [H_counter, this]
    have hlim0 : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (H_counter 1 y)) :=
      hlim.congr' h0
    have h1 : H_counter 1 y = 1 := by simp [H_counter]
    rw [tendsto_const_nhds_iff] at hlim0
    simp [h1] at hlim0
  have deriv_H_counter : ∀ (y : ℝ) (x : ℝ) (_ : x ≤ 1), deriv (fun t => H_counter t y) x = 0 := by
    intro y x hx
    dsimp [H_counter]
    rcases lt_or_eq_of_le hx with hx1 | rfl
    · have : (fun t => if t ≥ 1 then (1 : ℝ) else 0) =ᶠ[nhds x] (fun _ => 0) := by
        filter_upwards [IsOpen.mem_nhds isOpen_Iio hx1] with t ht
        have : ¬ (t ≥ 1) := not_le_of_gt ht
        simp [this]
      rw [this.deriv_eq, deriv_const]
    · exact deriv_zero_of_not_differentiableAt (H_counter_not_diff y)
  have H_counter_kernel : is_k_submod_kernel H_counter := by
    refine ⟨by simp [H_counter], by norm_num [H_counter], ?_, ?_, ?_, ?_, ?_⟩
    · intro x y hx0 hx1 hy0 hy1
      dsimp [H_counter]
      split_ifs <;> linarith
    · intro x1 x2 y hx1 hx12 hx2 hy0 hy1
      dsimp [H_counter]
      split_ifs <;> linarith
    · intro x y1 y2 hx0 hx1 hy1 hy12 hy2
      dsimp [H_counter]
      split_ifs <;> linarith
    · intro x1 x2 y1 y2 hx1 hx12 hx2 hy1 hy12 hy2
      rw [deriv_H_counter y2 x2 hx2, deriv_H_counter y1 x1 (by linarith)]
    · intro x1 x2 y1 y2 hx1 hx12 hx2 hy1 hy12 hy2
      have e2 : (fun t => H_counter x2 t) = fun _ => H_counter x2 0 := by ext; rfl
      have e1 : (fun t => H_counter x1 t) = fun _ => H_counter x1 0 := by ext; rfl
      rw [e2, e1, deriv_const, deriv_const]
  let σ2 : Fin 2 → Fin 2 := fun _ => 0
  let x : Fin 2 → Option (Fin 2) := fun _ => none
  let y : Fin 2 → Option (Fin 2) := fun e => if e = 0 then some 0 else none
  intro hall
  have hspec := hall (by decide : 0 < 2) (by decide : 2 ≤ 2) σ2 H_counter H_counter_kernel
  have hle : k_submod_le x y := by
    intro e; left; rfl
  have hy1 : y 1 = none := by rfl
  have hdim := hspec x y 1 0 hle hy1
  unfold k_submod_hidden_fn at hdim
  have hc_y' : ({e : Fin 2 | Function.update y 1 (some (0 : Fin 2)) e = some (σ2 e)} : Finset (Fin 2)).card = 2 := by
    have : ({e : Fin 2 | Function.update y 1 (some (0 : Fin 2)) e = some (σ2 e)} : Finset (Fin 2)) = Finset.univ := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hm_y' : ({e : Fin 2 | Function.update y 1 (some (0 : Fin 2)) e ≠ none} : Finset (Fin 2)).card = 2 := by
    have : ({e : Fin 2 | Function.update y 1 (some (0 : Fin 2)) e ≠ none} : Finset (Fin 2)) = Finset.univ := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hc_y : ({e : Fin 2 | y e = some (σ2 e)} : Finset (Fin 2)).card = 1 := by
    have : ({e : Fin 2 | y e = some (σ2 e)} : Finset (Fin 2)) = {0} := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hm_y : ({e : Fin 2 | y e ≠ none} : Finset (Fin 2)).card = 1 := by
    have : ({e : Fin 2 | y e ≠ none} : Finset (Fin 2)) = {0} := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hc_x' : ({e : Fin 2 | Function.update x 1 (some (0 : Fin 2)) e = some (σ2 e)} : Finset (Fin 2)).card = 1 := by
    have : ({e : Fin 2 | Function.update x 1 (some (0 : Fin 2)) e = some (σ2 e)} : Finset (Fin 2)) = {1} := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hm_x' : ({e : Fin 2 | Function.update x 1 (some (0 : Fin 2)) e ≠ none} : Finset (Fin 2)).card = 1 := by
    have : ({e : Fin 2 | Function.update x 1 (some (0 : Fin 2)) e ≠ none} : Finset (Fin 2)) = {1} := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hc_x : ({e : Fin 2 | x e = some (σ2 e)} : Finset (Fin 2)).card = 0 := by
    have : ({e : Fin 2 | x e = some (σ2 e)} : Finset (Fin 2)) = ∅ := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hm_x : ({e : Fin 2 | x e ≠ none} : Finset (Fin 2)).card = 0 := by
    have : ({e : Fin 2 | x e ≠ none} : Finset (Fin 2)) = ∅ := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  rw [hc_y', hm_y', hc_y, hm_y, hc_x', hm_x', hc_x, hm_x] at hdim
  dsimp [H_counter] at hdim
  norm_num at hdim
