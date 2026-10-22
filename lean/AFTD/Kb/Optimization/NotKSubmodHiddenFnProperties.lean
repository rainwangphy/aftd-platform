import AFTD.Prelude
import AFTD.Kb.Optimization.IsKSubmodKernel
import AFTD.Kb.Optimization.KSubmodHiddenFn
import AFTD.Kb.Optimization.IsKSubmodMonotone
import AFTD.Kb.Optimization.IsKSubmodular
import AFTD.Kb.Optimization.KSubmodJoin
import AFTD.Kb.Optimization.KSubmodMeet

/-!
# not_k_submod_hidden_fn_properties

Topic: submodular   Node: bf5f313dd92b

Provenance: original. Related work: refutes `k_submod_hidden_fn_properties`

The statement `k_submod_hidden_fn_properties` is false: The definition `is_k_submod_kernel` lacks a differentiability/continuity hypothesis on H. In Lean, `deriv f x` evaluates to 0 when f is not differentiable at x. Consequently, discontinuous functions like H(x, y) = if x ≥ 1 then 1 else 0 satisfy `is_k_submod_kernel H` because their derivatives vanish identically on [0,1]², satisfying conditions 6 and 7 vacuously. For this kernel, with n=2, k=2, σ ≡ 0, x = (some 0, none), y = (none, some 0), we find f(x ⊓ y) = 0, f(x ⊔ y) = 1, and f(x) = f(y) = 0, so f(x ⊓ y) + f(x ⊔ y) = 1 > 0 = f(x) + f(y), contradicting k-submodularity.
-/

theorem not_k_submod_hidden_fn_properties : ¬ (∀ {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (σ : Fin n → Fin k)
    (H : ℝ → ℝ → ℝ) (hH : is_k_submod_kernel H), let f := k_submod_hidden_fn H σ
    (∀ x, 0 ≤ f x) ∧
    is_k_submod_monotone f ∧
    is_k_submodular f ∧
    f (fun _ => none) = 0 ∧
    (∀ x, f x ≤ 1) ∧
    f (fun e => some (σ e)) = 1) := by
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
  let x2 : Fin 2 → Option (Fin 2) := fun e => if e = 0 then some 0 else none
  let y2 : Fin 2 → Option (Fin 2) := fun e => if e = 1 then some 0 else none
  have meet_eq : k_submod_meet x2 y2 = fun _ => none := by
    ext e; fin_cases e <;> rfl
  have join_eq : k_submod_join x2 y2 = fun _ => some 0 := by
    ext e; fin_cases e <;> rfl
  intro hall
  have hspec := hall (by decide : 0 < 2) (by decide : 2 ≤ 2) σ2 H_counter H_counter_kernel
  dsimp only at hspec
  rcases hspec with ⟨-, -, hsub, -⟩
  have h := hsub x2 y2
  unfold k_submod_hidden_fn at h
  have hc_x : ({e : Fin 2 | x2 e = some (σ2 e)} : Finset (Fin 2)).card = 1 := by
    have : ({e : Fin 2 | x2 e = some (σ2 e)} : Finset (Fin 2)) = {0} := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hm_x : ({e : Fin 2 | x2 e ≠ none} : Finset (Fin 2)).card = 1 := by
    have : ({e : Fin 2 | x2 e ≠ none} : Finset (Fin 2)) = {0} := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hc_y : ({e : Fin 2 | y2 e = some (σ2 e)} : Finset (Fin 2)).card = 1 := by
    have : ({e : Fin 2 | y2 e = some (σ2 e)} : Finset (Fin 2)) = {1} := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hm_y : ({e : Fin 2 | y2 e ≠ none} : Finset (Fin 2)).card = 1 := by
    have : ({e : Fin 2 | y2 e ≠ none} : Finset (Fin 2)) = {1} := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hc_m : ({e : Fin 2 | k_submod_meet x2 y2 e = some (σ2 e)} : Finset (Fin 2)).card = 0 := by
    rw [meet_eq]
    have : ({e : Fin 2 | (fun _ => (none : Option (Fin 2))) e = some (σ2 e)} : Finset (Fin 2)) = ∅ := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hm_m : ({e : Fin 2 | k_submod_meet x2 y2 e ≠ none} : Finset (Fin 2)).card = 0 := by
    rw [meet_eq]
    have : ({e : Fin 2 | (fun _ => (none : Option (Fin 2))) e ≠ none} : Finset (Fin 2)) = ∅ := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hc_j : ({e : Fin 2 | k_submod_join x2 y2 e = some (σ2 e)} : Finset (Fin 2)).card = 2 := by
    rw [join_eq]
    have : ({e : Fin 2 | (fun _ => some (0 : Fin 2)) e = some (σ2 e)} : Finset (Fin 2)) = Finset.univ := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  have hm_j : ({e : Fin 2 | k_submod_join x2 y2 e ≠ none} : Finset (Fin 2)).card = 2 := by
    rw [join_eq]
    have : ({e : Fin 2 | (fun _ => some (0 : Fin 2)) e ≠ none} : Finset (Fin 2)) = Finset.univ := by
      ext a; fin_cases a <;> decide
    rw [this]; rfl
  rw [hc_x, hm_x, hc_y, hm_y, hc_m, hm_m, hc_j, hm_j] at h
  dsimp [H_counter] at h
  norm_num at h
