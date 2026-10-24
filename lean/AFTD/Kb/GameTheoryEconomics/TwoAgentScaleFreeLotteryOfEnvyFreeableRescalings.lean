import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AllocationBundle
import AFTD.Kb.GameTheoryEconomics.AllocationIsEnvyFreeable
import AFTD.Kb.GameTheoryEconomics.TwoAgentEnvyFreeableIff

/-!
# two_agent_scale_free_lottery_of_envy_freeable_rescalings

Topic: fair_division   Node: 85eb2705b230

Provenance: helper lemma. step towards two_agent_converse_theorem

For two agents and any scale-free allocation property P, if every positive rescaling c ⊙ v admits an allocation that is simultaneously P and envy-freeable, then there exists an ex-ante envy-free lottery supported on allocations satisfying P.
-/

open Finset BigOperators

def two_agent_scale_free_lottery_d0
    {M : Type*} [Fintype M]
    (v : Fin 2 → Finset M → ℝ) (A : M → Fin 2) : ℝ :=
  v 0 (allocation_bundle A 0) - v 0 (allocation_bundle A 1)

def two_agent_scale_free_lottery_d1
    {M : Type*} [Fintype M]
    (v : Fin 2 → Finset M → ℝ) (A : M → Fin 2) : ℝ :=
  v 1 (allocation_bundle A 1) - v 1 (allocation_bundle A 0)

theorem two_agent_scale_free_lottery_case1
    {M : Type*} [Fintype M] [DecidableEq M]
    (v : Fin 2 → Finset M → ℝ)
    (P : (Fin 2 → Finset M → ℝ) → (M → Fin 2) → Prop)
    (A : M → Fin 2) (hPA : P v A)
    (h0 : 0 ≤ two_agent_scale_free_lottery_d0 v A)
    (h1 : 0 ≤ two_agent_scale_free_lottery_d1 v A) :
    ∃ q : (M → Fin 2) → ℝ, (∀ A, 0 ≤ q A) ∧ ∑ A, q A = 1 ∧
      (∀ i j, ∑ A, q A * v i (allocation_bundle A j) ≤ ∑ A, q A * v i (allocation_bundle A i)) ∧
      (∀ A, 0 < q A → P v A) := by
  let q : (M → Fin 2) → ℝ := fun x => if x = A then 1 else 0
  use q
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    dsimp [q]
    split_ifs <;> linarith
  · dsimp [q]
    simp
  · intro i j
    have hq : ∀ f : (M → Fin 2) → ℝ, ∑ x, q x * f x = f A := by
      intro f
      dsimp [q]
      have : (fun x => (if x = A then (1 : ℝ) else 0) * f x) = (fun x => if x = A then f A else 0) := by
        funext x
        split_ifs with h
        · subst h; ring
        · ring
      rw [this]
      simp
    rw [hq, hq]
    fin_cases i <;> fin_cases j
    · rfl
    · change v 0 (allocation_bundle A 1) ≤ v 0 (allocation_bundle A 0)
      dsimp [two_agent_scale_free_lottery_d0] at h0
      linarith
    · change v 1 (allocation_bundle A 0) ≤ v 1 (allocation_bundle A 1)
      dsimp [two_agent_scale_free_lottery_d1] at h1
      linarith
    · rfl
  · intro x hx
    dsimp [q] at hx
    split_ifs at hx with h
    · subst h; exact hPA
    · linarith

theorem two_agent_scale_free_lottery_case2
    {M : Type*} [Fintype M] [DecidableEq M]
    (v : Fin 2 → Finset M → ℝ)
    (P : (Fin 2 → Finset M → ℝ) → (M → Fin 2) → Prop)
    (A₁ A₂ : M → Fin 2) (hPA₁ : P v A₁) (hPA₂ : P v A₂)
    (hpos : 0 < two_agent_scale_free_lottery_d0 v A₁)
    (hneg : two_agent_scale_free_lottery_d0 v A₂ < 0)
    (hdet : 0 ≤ two_agent_scale_free_lottery_d0 v A₁ * two_agent_scale_free_lottery_d1 v A₂ -
                two_agent_scale_free_lottery_d0 v A₂ * two_agent_scale_free_lottery_d1 v A₁) :
    ∃ q : (M → Fin 2) → ℝ, (∀ A, 0 ≤ q A) ∧ ∑ A, q A = 1 ∧
      (∀ i j, ∑ A, q A * v i (allocation_bundle A j) ≤ ∑ A, q A * v i (allocation_bundle A i)) ∧
      (∀ A, 0 < q A → P v A) := by
  have hne : A₁ ≠ A₂ := by
    rintro rfl
    linarith
  have hdenom : 0 < two_agent_scale_free_lottery_d0 v A₁ - two_agent_scale_free_lottery_d0 v A₂ := by linarith
  have hdenom_ne : two_agent_scale_free_lottery_d0 v A₁ - two_agent_scale_free_lottery_d0 v A₂ ≠ 0 := by linarith
  let α : ℝ := - two_agent_scale_free_lottery_d0 v A₂ / (two_agent_scale_free_lottery_d0 v A₁ - two_agent_scale_free_lottery_d0 v A₂)
  let β : ℝ := two_agent_scale_free_lottery_d0 v A₁ / (two_agent_scale_free_lottery_d0 v A₁ - two_agent_scale_free_lottery_d0 v A₂)
  have hsum : α + β = 1 := by
    dsimp [α, β]
    rw [← add_div]
    have : -two_agent_scale_free_lottery_d0 v A₂ + two_agent_scale_free_lottery_d0 v A₁ =
           two_agent_scale_free_lottery_d0 v A₁ - two_agent_scale_free_lottery_d0 v A₂ := by ring
    rw [this, div_self hdenom_ne]
  let q : (M → Fin 2) → ℝ := fun x => if x = A₁ then α else if x = A₂ then β else 0
  have hq_eval : ∀ f : (M → Fin 2) → ℝ, ∑ x, q x * f x = α * f A₁ + β * f A₂ := by
    intro f
    dsimp [q]
    have : (fun x => (if x = A₁ then α else if x = A₂ then β else 0) * f x) =
           (fun x => (if x = A₁ then α * f x else 0) + (if x = A₂ then β * f x else 0)) := by
      funext x
      split_ifs with h1 h2
      · subst h1; subst h2; exact (hne rfl).elim
      · ring
      · ring
      · ring
    rw [this, sum_add_distrib]
    simp
  have hq_sum : ∑ x, q x = 1 := by
    have := hq_eval (fun _ => 1)
    simpa [hsum] using this
  use q
  refine ⟨?_, hq_sum, ?_, ?_⟩
  · intro x
    dsimp [q]
    split_ifs <;> linarith [div_nonneg (by linarith : 0 ≤ -two_agent_scale_free_lottery_d0 v A₂) (by linarith : 0 ≤ two_agent_scale_free_lottery_d0 v A₁ - two_agent_scale_free_lottery_d0 v A₂),
                           div_nonneg (by linarith : 0 ≤ two_agent_scale_free_lottery_d0 v A₁) (by linarith : 0 ≤ two_agent_scale_free_lottery_d0 v A₁ - two_agent_scale_free_lottery_d0 v A₂)]
  · intro i j
    have hd0 : 0 ≤ ∑ A, q A * (v 0 (allocation_bundle A 0) - v 0 (allocation_bundle A 1)) := by
      rw [hq_eval]
      have : α * (v 0 (allocation_bundle A₁ 0) - v 0 (allocation_bundle A₁ 1)) +
             β * (v 0 (allocation_bundle A₂ 0) - v 0 (allocation_bundle A₂ 1)) = 0 := by
        dsimp [α, β, two_agent_scale_free_lottery_d0]
        field_simp
        ring
      rw [this]
    have hd1 : 0 ≤ ∑ A, q A * (v 1 (allocation_bundle A 1) - v 1 (allocation_bundle A 0)) := by
      rw [hq_eval]
      have : α * (v 1 (allocation_bundle A₁ 1) - v 1 (allocation_bundle A₁ 0)) +
             β * (v 1 (allocation_bundle A₂ 1) - v 1 (allocation_bundle A₂ 0)) =
             (two_agent_scale_free_lottery_d0 v A₁ * two_agent_scale_free_lottery_d1 v A₂ -
              two_agent_scale_free_lottery_d0 v A₂ * two_agent_scale_free_lottery_d1 v A₁) /
             (two_agent_scale_free_lottery_d0 v A₁ - two_agent_scale_free_lottery_d0 v A₂) := by
        dsimp [α, β, two_agent_scale_free_lottery_d0, two_agent_scale_free_lottery_d1]
        field_simp
        ring
      rw [this]
      exact div_nonneg hdet (by linarith)
    fin_cases i <;> fin_cases j
    · rfl
    · change ∑ A, q A * v 0 (allocation_bundle A 1) ≤ ∑ A, q A * v 0 (allocation_bundle A 0)
      have : ∑ A, q A * v 0 (allocation_bundle A 0) - ∑ A, q A * v 0 (allocation_bundle A 1) =
        ∑ A, q A * (v 0 (allocation_bundle A 0) - v 0 (allocation_bundle A 1)) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro x _
        ring
      linarith
    · change ∑ A, q A * v 1 (allocation_bundle A 0) ≤ ∑ A, q A * v 1 (allocation_bundle A 1)
      have : ∑ A, q A * v 1 (allocation_bundle A 1) - ∑ A, q A * v 1 (allocation_bundle A 0) =
        ∑ A, q A * (v 1 (allocation_bundle A 1) - v 1 (allocation_bundle A 0)) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro x _
        ring
      linarith
    · rfl
  · intro x hx
    dsimp [q] at hx
    split_ifs at hx with h1 h2
    · subst h1; exact hPA₁
    · subst h2; exact hPA₂
    · linarith

theorem two_agent_scale_free_lottery_exists_good_or_pair
    {M : Type*} [Fintype M] [DecidableEq M]
    (v : Fin 2 → Finset M → ℝ)
    (P : (Fin 2 → Finset M → ℝ) → (M → Fin 2) → Prop)
    (hP : ∀ (v' : Fin 2 → Finset M → ℝ) (c : Fin 2 → ℝ), (∀ i, 0 < c i) →
      ∀ A, P (fun i S => c i * v' i S) A ↔ P v' A)
    (h : ∀ c : Fin 2 → ℝ, (∀ i, 0 < c i) →
      ∃ A : M → Fin 2, P (fun i S => c i * v i S) A ∧
        allocation_is_envy_freeable (fun i S => c i * v i S) A) :
    (∃ A, P v A ∧ 0 ≤ two_agent_scale_free_lottery_d0 v A ∧ 0 ≤ two_agent_scale_free_lottery_d1 v A) ∨
    (∃ A₁ A₂, P v A₁ ∧ P v A₂ ∧ 0 < two_agent_scale_free_lottery_d0 v A₁ ∧ two_agent_scale_free_lottery_d0 v A₂ < 0 ∧
      0 ≤ two_agent_scale_free_lottery_d0 v A₁ * two_agent_scale_free_lottery_d1 v A₂ -
          two_agent_scale_free_lottery_d0 v A₂ * two_agent_scale_free_lottery_d1 v A₁) := by
  classical
  by_contra h_not
  have ⟨hn1, hn2⟩ := not_or.mp h_not
  have h_not1' : ∀ A, P v A → 0 ≤ two_agent_scale_free_lottery_d0 v A → two_agent_scale_free_lottery_d1 v A < 0 := by
    intro A hPA hd0
    by_contra hc
    apply hn1
    exact ⟨A, hPA, hd0, by linarith⟩
  have h_not2' : ∀ A₁ A₂, P v A₁ → P v A₂ → 0 < two_agent_scale_free_lottery_d0 v A₁ → two_agent_scale_free_lottery_d0 v A₂ < 0 →
      two_agent_scale_free_lottery_d0 v A₁ * two_agent_scale_free_lottery_d1 v A₂ -
      two_agent_scale_free_lottery_d0 v A₂ * two_agent_scale_free_lottery_d1 v A₁ < 0 := by
    intro A₁ A₂ h1 h2 hd1 hd2
    by_contra hc
    apply hn2
    exact ⟨A₁, A₂, h1, h2, hd1, hd2, by linarith⟩
  let s : Finset (M → Fin 2) := Finset.univ.filter (fun A => P v A)
  have hs_mem : ∀ A, A ∈ s ↔ P v A := by
    intro A
    simp [s]
  let s_pos := s.filter (fun A => 0 < two_agent_scale_free_lottery_d0 v A)
  let s_neg := s.filter (fun A => two_agent_scale_free_lottery_d0 v A < 0)
  have hk_exists : ∃ k > 0,
      (∀ A ∈ s, 0 < two_agent_scale_free_lottery_d0 v A → k < -two_agent_scale_free_lottery_d1 v A / two_agent_scale_free_lottery_d0 v A) ∧
      (∀ A ∈ s, two_agent_scale_free_lottery_d0 v A < 0 → two_agent_scale_free_lottery_d1 v A / -two_agent_scale_free_lottery_d0 v A < k) := by
    by_cases hp : s_pos.Nonempty
    · by_cases hn : s_neg.Nonempty
      · rcases Finset.exists_min_image s_pos (fun A => -two_agent_scale_free_lottery_d1 v A / two_agent_scale_free_lottery_d0 v A) hp with ⟨Amin, hAmin, hmin⟩
        rcases Finset.exists_max_image s_neg (fun A => two_agent_scale_free_lottery_d1 v A / -two_agent_scale_free_lottery_d0 v A) hn with ⟨Amax, hAmax, hmax⟩
        have hAmin_s : Amin ∈ s := (Finset.mem_filter.mp hAmin).1
        have hAmin_pos : 0 < two_agent_scale_free_lottery_d0 v Amin := (Finset.mem_filter.mp hAmin).2
        have hAmax_s : Amax ∈ s := (Finset.mem_filter.mp hAmax).1
        have hAmax_neg : two_agent_scale_free_lottery_d0 v Amax < 0 := (Finset.mem_filter.mp hAmax).2
        have hPAmin : P v Amin := (hs_mem Amin).mp hAmin_s
        have hPAmax : P v Amax := (hs_mem Amax).mp hAmax_s
        have hAmin_d1 : two_agent_scale_free_lottery_d1 v Amin < 0 := h_not1' Amin hPAmin (by linarith)
        let m := -two_agent_scale_free_lottery_d1 v Amin / two_agent_scale_free_lottery_d0 v Amin
        let M := two_agent_scale_free_lottery_d1 v Amax / -two_agent_scale_free_lottery_d0 v Amax
        have hm_pos : 0 < m := div_pos (by linarith) hAmin_pos
        have hdet := h_not2' Amin Amax hPAmin hPAmax hAmin_pos hAmax_neg
        have hlt : M < m := by
          have ha : 0 < two_agent_scale_free_lottery_d0 v Amin := hAmin_pos
          have hc : two_agent_scale_free_lottery_d0 v Amax < 0 := hAmax_neg
          have h1 : 0 < -two_agent_scale_free_lottery_d0 v Amax := by linarith
          have hpos : 0 < two_agent_scale_free_lottery_d0 v Amin * (-two_agent_scale_free_lottery_d0 v Amax) := mul_pos ha h1
          have h_eq : two_agent_scale_free_lottery_d1 v Amax / (-two_agent_scale_free_lottery_d0 v Amax) - -two_agent_scale_free_lottery_d1 v Amin / two_agent_scale_free_lottery_d0 v Amin =
              (two_agent_scale_free_lottery_d0 v Amin * two_agent_scale_free_lottery_d1 v Amax - two_agent_scale_free_lottery_d0 v Amax * two_agent_scale_free_lottery_d1 v Amin) /
              (two_agent_scale_free_lottery_d0 v Amin * -two_agent_scale_free_lottery_d0 v Amax) := by
            have ha' : two_agent_scale_free_lottery_d0 v Amin ≠ 0 := by linarith
            have hc' : -two_agent_scale_free_lottery_d0 v Amax ≠ 0 := by linarith
            rw [sub_eq_iff_eq_add, add_comm]
            have : two_agent_scale_free_lottery_d0 v Amin * two_agent_scale_free_lottery_d1 v Amax - two_agent_scale_free_lottery_d0 v Amax * two_agent_scale_free_lottery_d1 v Amin =
                   two_agent_scale_free_lottery_d0 v Amin * two_agent_scale_free_lottery_d1 v Amax + (-two_agent_scale_free_lottery_d0 v Amax) * two_agent_scale_free_lottery_d1 v Amin := by ring
            rw [this, add_div]
            have h_left : two_agent_scale_free_lottery_d0 v Amin * two_agent_scale_free_lottery_d1 v Amax / (two_agent_scale_free_lottery_d0 v Amin * -two_agent_scale_free_lottery_d0 v Amax) =
                          two_agent_scale_free_lottery_d1 v Amax / -two_agent_scale_free_lottery_d0 v Amax := by
              rw [mul_div_mul_left (two_agent_scale_free_lottery_d1 v Amax) (-two_agent_scale_free_lottery_d0 v Amax) ha']
            have h_right : (-two_agent_scale_free_lottery_d0 v Amax) * two_agent_scale_free_lottery_d1 v Amin / (two_agent_scale_free_lottery_d0 v Amin * -two_agent_scale_free_lottery_d0 v Amax) =
                           two_agent_scale_free_lottery_d1 v Amin / two_agent_scale_free_lottery_d0 v Amin := by
              rw [mul_comm (two_agent_scale_free_lottery_d0 v Amin) (-two_agent_scale_free_lottery_d0 v Amax), mul_div_mul_left (two_agent_scale_free_lottery_d1 v Amin) (two_agent_scale_free_lottery_d0 v Amin) hc']
            rw [h_left, h_right]
            ring
          have h_neg : (two_agent_scale_free_lottery_d0 v Amin * two_agent_scale_free_lottery_d1 v Amax - two_agent_scale_free_lottery_d0 v Amax * two_agent_scale_free_lottery_d1 v Amin) /
                       (two_agent_scale_free_lottery_d0 v Amin * -two_agent_scale_free_lottery_d0 v Amax) < 0 :=
            div_neg_of_neg_of_pos hdet hpos
          dsimp [M, m]
          linarith [h_eq, h_neg]
        have h_max_lt : max 0 M < m := by
          rw [max_lt_iff]
          exact ⟨hm_pos, hlt⟩
        let k := (max 0 M + m) / 2
        have hk_pos : 0 < k := by
          dsimp [k]
          have : 0 ≤ max 0 M := le_max_left 0 M
          linarith
        have hM_lt_k : M < k := by
          dsimp [k]
          have : M ≤ max 0 M := le_max_right 0 M
          linarith
        have hk_lt_m : k < m := by
          dsimp [k]
          linarith
        use k, hk_pos
        refine ⟨?_, ?_⟩
        · intro A hAs hApos
          have hA_pos_mem : A ∈ s_pos := Finset.mem_filter.mpr ⟨hAs, hApos⟩
          have hle := hmin A hA_pos_mem
          change m ≤ -two_agent_scale_free_lottery_d1 v A / two_agent_scale_free_lottery_d0 v A at hle
          linarith
        · intro A hAs hAneg
          have hA_neg_mem : A ∈ s_neg := Finset.mem_filter.mpr ⟨hAs, hAneg⟩
          have hle := hmax A hA_neg_mem
          change two_agent_scale_free_lottery_d1 v A / -two_agent_scale_free_lottery_d0 v A ≤ M at hle
          linarith
      · -- hp and ¬hn
        rcases Finset.exists_min_image s_pos (fun A => -two_agent_scale_free_lottery_d1 v A / two_agent_scale_free_lottery_d0 v A) hp with ⟨Amin, hAmin, hmin⟩
        have hAmin_s : Amin ∈ s := (Finset.mem_filter.mp hAmin).1
        have hAmin_pos : 0 < two_agent_scale_free_lottery_d0 v Amin := (Finset.mem_filter.mp hAmin).2
        have hPAmin : P v Amin := (hs_mem Amin).mp hAmin_s
        have hAmin_d1 : two_agent_scale_free_lottery_d1 v Amin < 0 := h_not1' Amin hPAmin (by linarith)
        let m := -two_agent_scale_free_lottery_d1 v Amin / two_agent_scale_free_lottery_d0 v Amin
        have hm_pos : 0 < m := div_pos (by linarith) hAmin_pos
        use m / 2, by linarith
        refine ⟨?_, ?_⟩
        · intro A hAs hApos
          have hA_pos_mem : A ∈ s_pos := Finset.mem_filter.mpr ⟨hAs, hApos⟩
          have hle := hmin A hA_pos_mem
          change m ≤ -two_agent_scale_free_lottery_d1 v A / two_agent_scale_free_lottery_d0 v A at hle
          linarith
        · intro A hAs hAneg
          have : A ∈ s_neg := Finset.mem_filter.mpr ⟨hAs, hAneg⟩
          exact (hn ⟨A, this⟩).elim
    · by_cases hn : s_neg.Nonempty
      · -- ¬hp and hn
        rcases Finset.exists_max_image s_neg (fun A => two_agent_scale_free_lottery_d1 v A / -two_agent_scale_free_lottery_d0 v A) hn with ⟨Amax, hAmax, hmax⟩
        let M := two_agent_scale_free_lottery_d1 v Amax / -two_agent_scale_free_lottery_d0 v Amax
        let k := max 0 M + 1
        have hk_pos : 0 < k := by
          dsimp [k]
          have : 0 ≤ max 0 M := le_max_left 0 M
          linarith
        use k, hk_pos
        refine ⟨?_, ?_⟩
        · intro A hAs hApos
          have : A ∈ s_pos := Finset.mem_filter.mpr ⟨hAs, hApos⟩
          exact (hp ⟨A, this⟩).elim
        · intro A hAs hAneg
          have hA_neg_mem : A ∈ s_neg := Finset.mem_filter.mpr ⟨hAs, hAneg⟩
          have hle := hmax A hA_neg_mem
          change two_agent_scale_free_lottery_d1 v A / -two_agent_scale_free_lottery_d0 v A ≤ M at hle
          have : M ≤ max 0 M := le_max_right 0 M
          linarith
      · -- ¬hp and ¬hn
        use 1, by norm_num
        refine ⟨?_, ?_⟩
        · intro A hAs hApos
          have : A ∈ s_pos := Finset.mem_filter.mpr ⟨hAs, hApos⟩
          exact (hp ⟨A, this⟩).elim
        · intro A hAs hAneg
          have : A ∈ s_neg := Finset.mem_filter.mpr ⟨hAs, hAneg⟩
          exact (hn ⟨A, this⟩).elim
  rcases hk_exists with ⟨k, hk_pos, hk_upper, hk_lower⟩
  let c : Fin 2 → ℝ := fun j => if j = 0 then k else 1
  have hc : ∀ i, 0 < c i := by
    intro i
    fin_cases i <;> simp [c, hk_pos]
  rcases h c hc with ⟨A, hPA_c, hEF_c⟩
  have hPA : P v A := (hP v c hc A).mp hPA_c
  have hAs : A ∈ s := (hs_mem A).mpr hPA
  rw [two_agent_envy_freeable_iff] at hEF_c
  have hcalc : (c 0 * v 0 (allocation_bundle A 0) - c 0 * v 0 (allocation_bundle A 1)) +
      (c 1 * v 1 (allocation_bundle A 1) - c 1 * v 1 (allocation_bundle A 0)) =
      k * two_agent_scale_free_lottery_d0 v A + two_agent_scale_free_lottery_d1 v A := by
    have hc0 : c 0 = k := by rfl
    have hc1 : c 1 = 1 := by rfl
    dsimp [two_agent_scale_free_lottery_d0, two_agent_scale_free_lottery_d1]
    rw [hc0, hc1]
    ring
  rw [hcalc] at hEF_c
  have h_lt : k * two_agent_scale_free_lottery_d0 v A + two_agent_scale_free_lottery_d1 v A < 0 := by
    rcases lt_trichotomy (two_agent_scale_free_lottery_d0 v A) 0 with hAneg | hAzero | hApos
    · have hk := hk_lower A hAs hAneg
      have hpos : 0 < -two_agent_scale_free_lottery_d0 v A := by linarith
      have : two_agent_scale_free_lottery_d1 v A < k * (-two_agent_scale_free_lottery_d0 v A) := (div_lt_iff₀ hpos).mp hk
      linarith
    · have : two_agent_scale_free_lottery_d1 v A < 0 := h_not1' A hPA (by linarith)
      rw [hAzero]
      linarith
    · have hk := hk_upper A hAs hApos
      have : k * two_agent_scale_free_lottery_d0 v A < -two_agent_scale_free_lottery_d1 v A := (lt_div_iff₀ hApos).mp hk
      linarith
  linarith

/-- Theorem 3.1 of arXiv:2610.14994 for two agents: for any scale-free allocation property P, if every coordinatewise positive rescaling c ⊙ v admits an allocation that is simultaneously P and envy-freeable, then there exists an ex-ante envy-free lottery supported on P. -/
theorem two_agent_scale_free_lottery_of_envy_freeable_rescalings
    {M : Type*} [Fintype M] [DecidableEq M]
    (v : Fin 2 → Finset M → ℝ)
    (P : (Fin 2 → Finset M → ℝ) → (M → Fin 2) → Prop)
    (hP : ∀ (v' : Fin 2 → Finset M → ℝ) (c : Fin 2 → ℝ), (∀ i, 0 < c i) →
      ∀ A, P (fun i S => c i * v' i S) A ↔ P v' A)
    (h : ∀ c : Fin 2 → ℝ, (∀ i, 0 < c i) →
      ∃ A : M → Fin 2, P (fun i S => c i * v i S) A ∧
        allocation_is_envy_freeable (fun i S => c i * v i S) A) :
    ∃ q : (M → Fin 2) → ℝ, (∀ A, 0 ≤ q A) ∧ ∑ A, q A = 1 ∧
      (∀ i j, ∑ A, q A * v i (allocation_bundle A j) ≤ ∑ A, q A * v i (allocation_bundle A i)) ∧
      (∀ A, 0 < q A → P v A) := by
  rcases two_agent_scale_free_lottery_exists_good_or_pair v P hP h with ⟨A, hPA, h0, h1⟩ | ⟨A₁, A₂, hPA₁, hPA₂, hpos, hneg, hdet⟩
  · exact two_agent_scale_free_lottery_case1 v P A hPA h0 h1
  · exact two_agent_scale_free_lottery_case2 v P A₁ A₂ hPA₁ hPA₂ hpos hneg hdet
