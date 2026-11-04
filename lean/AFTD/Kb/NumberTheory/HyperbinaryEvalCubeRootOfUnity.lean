import AFTD.Prelude
import AFTD.Kb.NumberTheory.EisensteinOmega
import AFTD.Kb.NumberTheory.HyperbinaryLengthPoly

/-!
# hyperbinary_eval_cube_root_of_unity

Topic: elementary_number_theory   Node: dfc69200328b

Provenance: formalization of a published result. Source: scout/2611-01243-halving-partitions-and-hyperbinary-expansions.md:1200

For every non-negative integer m, evaluating the hyperbinary length polynomial H_m(z) at the primitive cube root of unity ω = (-1 + √(-3))/2 gives an element of {0, ±1, ±ω, ±ω²}.
-/

noncomputable def hyperbinary_eval_cube_root_of_unity_S : Set ℂ :=
  {0, 1, -1, eisensteinOmega, -eisensteinOmega, eisensteinOmega ^ 2, -eisensteinOmega ^ 2}

def hyperbinary_eval_cube_root_of_unity_ValidPair (x y : ℂ) : Prop :=
  (x = 0 ∧ y ∈ hyperbinary_eval_cube_root_of_unity_S) ∨
  (y = 0 ∧ x ∈ hyperbinary_eval_cube_root_of_unity_S) ∨
  (x ∈ hyperbinary_eval_cube_root_of_unity_S ∧ y = eisensteinOmega * x) ∨
  (x ∈ hyperbinary_eval_cube_root_of_unity_S ∧ y = -eisensteinOmega ^ 2 * x)

lemma hyperbinary_eval_cube_root_of_unity_valid_pair_fst_mem {x y : ℂ}
    (h : hyperbinary_eval_cube_root_of_unity_ValidPair x y) :
    x ∈ hyperbinary_eval_cube_root_of_unity_S := by
  rcases h with ⟨rfl, _⟩ | ⟨_, hx⟩ | ⟨hx, _⟩ | ⟨hx, _⟩
  · simp [hyperbinary_eval_cube_root_of_unity_S]
  · exact hx
  · exact hx
  · exact hx

lemma hyperbinary_eval_cube_root_of_unity_omega_sq_add_omega_add_one :
    eisensteinOmega ^ 2 + eisensteinOmega + 1 = 0 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  dsimp [eisensteinOmega]
  have h_div : ((-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2) ^ 2 = (-1 + Complex.I * Real.sqrt 3) ^ 2 / 4 := by ring
  rw [h_div]
  have : (-1 + Complex.I * (Real.sqrt 3 : ℂ)) ^ 2 = 1 - 2 * Complex.I * Real.sqrt 3 + Complex.I ^ 2 * (Real.sqrt 3 : ℂ) ^ 2 := by ring
  rw [this, hI, h3]
  ring

lemma hyperbinary_eval_cube_root_of_unity_omega_cube : eisensteinOmega ^ 3 = 1 := by
  have h := hyperbinary_eval_cube_root_of_unity_omega_sq_add_omega_add_one
  linear_combination (eisensteinOmega - 1) * h

lemma hyperbinary_eval_cube_root_of_unity_mem_S_neg (z : ℂ)
    (hz : z ∈ hyperbinary_eval_cube_root_of_unity_S) :
    -z ∈ hyperbinary_eval_cube_root_of_unity_S := by
  simp only [hyperbinary_eval_cube_root_of_unity_S, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left; ring
  · right; right; left; ring
  · right; left; ring
  · right; right; right; right; left; ring
  · right; right; right; left; ring
  · right; right; right; right; right; right; ring
  · right; right; right; right; right; left; ring

lemma hyperbinary_eval_cube_root_of_unity_mem_S_omega_mul (z : ℂ)
    (hz : z ∈ hyperbinary_eval_cube_root_of_unity_S) :
    eisensteinOmega * z ∈ hyperbinary_eval_cube_root_of_unity_S := by
  have h3 := hyperbinary_eval_cube_root_of_unity_omega_cube
  simp only [hyperbinary_eval_cube_root_of_unity_S, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left; ring
  · right; right; right; left; ring
  · right; right; right; right; left; ring
  · right; right; right; right; right; left; ring
  · right; right; right; right; right; right; ring
  · right; left
    calc eisensteinOmega * eisensteinOmega ^ 2 = eisensteinOmega ^ 3 := by ring
    _ = 1 := h3
  · right; right; left
    calc eisensteinOmega * -eisensteinOmega ^ 2 = -eisensteinOmega ^ 3 := by ring
    _ = -1 := by rw [h3]

lemma hyperbinary_eval_cube_root_of_unity_mem_S_omega_sq_mul (z : ℂ)
    (hz : z ∈ hyperbinary_eval_cube_root_of_unity_S) :
    eisensteinOmega ^ 2 * z ∈ hyperbinary_eval_cube_root_of_unity_S := by
  have : eisensteinOmega ^ 2 * z = eisensteinOmega * (eisensteinOmega * z) := by ring
  rw [this]
  exact hyperbinary_eval_cube_root_of_unity_mem_S_omega_mul _ (hyperbinary_eval_cube_root_of_unity_mem_S_omega_mul _ hz)

lemma hyperbinary_eval_cube_root_of_unity_valid_pair_step_odd {x y : ℂ}
    (h : hyperbinary_eval_cube_root_of_unity_ValidPair x y) :
    hyperbinary_eval_cube_root_of_unity_ValidPair (eisensteinOmega * x) (y + eisensteinOmega ^ 2 * x) := by
  have h_rel := hyperbinary_eval_cube_root_of_unity_omega_sq_add_omega_add_one
  rcases h with ⟨rfl, hy⟩ | ⟨rfl, hx⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩
  · left
    refine ⟨by ring, by simp [hy]⟩
  · right; right; left
    refine ⟨hyperbinary_eval_cube_root_of_unity_mem_S_omega_mul x hx, ?_⟩
    ring
  · right; right; right
    refine ⟨hyperbinary_eval_cube_root_of_unity_mem_S_omega_mul x hx, ?_⟩
    linear_combination eisensteinOmega * x * h_rel
  · right; left
    refine ⟨by ring, hyperbinary_eval_cube_root_of_unity_mem_S_omega_mul x hx⟩

lemma hyperbinary_eval_cube_root_of_unity_valid_pair_step_even {x y : ℂ}
    (h : hyperbinary_eval_cube_root_of_unity_ValidPair x y) :
    hyperbinary_eval_cube_root_of_unity_ValidPair (y + eisensteinOmega ^ 2 * x) (eisensteinOmega * y) := by
  have h_cube := hyperbinary_eval_cube_root_of_unity_omega_cube
  have h_rel := hyperbinary_eval_cube_root_of_unity_omega_sq_add_omega_add_one
  rcases h with ⟨rfl, hy⟩ | ⟨rfl, hx⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩
  · right; right; left
    refine ⟨by simpa using hy, by ring⟩
  · right; left
    refine ⟨by ring, by simpa using hyperbinary_eval_cube_root_of_unity_mem_S_omega_sq_mul x hx⟩
  · right; right; right
    have h_neg_x : -x ∈ hyperbinary_eval_cube_root_of_unity_S := hyperbinary_eval_cube_root_of_unity_mem_S_neg x hx
    refine ⟨?_, ?_⟩
    · have : eisensteinOmega * x + eisensteinOmega ^ 2 * x = -x := by
        linear_combination x * h_rel
      rw [this]
      exact h_neg_x
    · linear_combination eisensteinOmega ^ 2 * x * h_rel
  · left
    refine ⟨by ring, ?_⟩
    have : eisensteinOmega * (-eisensteinOmega ^ 2 * x) = -x := by
      linear_combination -x * h_cube
    rw [this]
    exact hyperbinary_eval_cube_root_of_unity_mem_S_neg x hx

noncomputable def hyperbinary_eval_cube_root_of_unity_H (m : ℕ) : ℂ :=
  Polynomial.aeval eisensteinOmega (hyperbinaryLengthPoly m)

lemma hyperbinary_eval_cube_root_of_unity_H_zero :
    hyperbinary_eval_cube_root_of_unity_H 0 = 1 := by
  dsimp [hyperbinary_eval_cube_root_of_unity_H]
  rw [hyperbinaryLengthPoly.eq_1]
  simp

lemma hyperbinary_eval_cube_root_of_unity_H_odd (k : ℕ) :
    hyperbinary_eval_cube_root_of_unity_H (2 * k + 1) = eisensteinOmega * hyperbinary_eval_cube_root_of_unity_H k := by
  dsimp [hyperbinary_eval_cube_root_of_unity_H]
  have h_succ : 2 * k + 1 = (2 * k).succ := rfl
  rw [h_succ, hyperbinaryLengthPoly.eq_2]
  have h_mod : (2 * k + 1) % 2 = 1 := by omega
  have h_div : (2 * k + 1) / 2 = k := by omega
  simp only [h_mod, ↓reduceDIte]
  rw [h_div]
  simp

lemma hyperbinary_eval_cube_root_of_unity_H_even (k : ℕ) :
    hyperbinary_eval_cube_root_of_unity_H (2 * k + 2) =
      hyperbinary_eval_cube_root_of_unity_H (k + 1) + eisensteinOmega ^ 2 * hyperbinary_eval_cube_root_of_unity_H k := by
  dsimp [hyperbinary_eval_cube_root_of_unity_H]
  have h_succ : 2 * k + 2 = (2 * k + 1).succ := rfl
  rw [h_succ, hyperbinaryLengthPoly.eq_2]
  have h_mod : ¬((2 * k + 1 + 1) % 2 = 1) := by omega
  have h_div1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp only [h_mod, ↓reduceDIte]
  rw [h_div1]
  simp

lemma hyperbinary_eval_cube_root_of_unity_H_one :
    hyperbinary_eval_cube_root_of_unity_H 1 = eisensteinOmega := by
  have : 1 = 2 * 0 + 1 := rfl
  rw [this, hyperbinary_eval_cube_root_of_unity_H_odd, hyperbinary_eval_cube_root_of_unity_H_zero, mul_one]

lemma hyperbinary_eval_cube_root_of_unity_H_pair_valid (m : ℕ) :
    hyperbinary_eval_cube_root_of_unity_ValidPair
      (hyperbinary_eval_cube_root_of_unity_H m) (hyperbinary_eval_cube_root_of_unity_H (m + 1)) := by
  induction' m using Nat.strong_induction_on with m ih
  rcases m with _ | m
  · rw [hyperbinary_eval_cube_root_of_unity_H_zero, hyperbinary_eval_cube_root_of_unity_H_one]
    right; right; left
    refine ⟨by simp [hyperbinary_eval_cube_root_of_unity_S], by ring⟩
  · by_cases hm : m.succ % 2 = 1
    · obtain ⟨k, hk_lt, hk_eq⟩ : ∃ k, k < m.succ ∧ m.succ = 2 * k + 1 := by
        refine ⟨m.succ / 2, ?_, ?_⟩ <;> omega
      have ih_k := ih k hk_lt
      have h1 : hyperbinary_eval_cube_root_of_unity_H m.succ =
          eisensteinOmega * hyperbinary_eval_cube_root_of_unity_H k := by
        rw [hk_eq, hyperbinary_eval_cube_root_of_unity_H_odd]
      have h2 : hyperbinary_eval_cube_root_of_unity_H (m.succ + 1) =
          hyperbinary_eval_cube_root_of_unity_H (k + 1) + eisensteinOmega ^ 2 * hyperbinary_eval_cube_root_of_unity_H k := by
        have : m.succ + 1 = 2 * k + 2 := by omega
        rw [this, hyperbinary_eval_cube_root_of_unity_H_even]
      rw [h1, h2]
      exact hyperbinary_eval_cube_root_of_unity_valid_pair_step_odd ih_k
    · obtain ⟨k, hk_lt, hk_eq⟩ : ∃ k, k < m.succ ∧ m.succ = 2 * k + 2 := by
        refine ⟨m.succ / 2 - 1, ?_, ?_⟩ <;> omega
      have ih_k := ih k hk_lt
      have h1 : hyperbinary_eval_cube_root_of_unity_H m.succ =
          hyperbinary_eval_cube_root_of_unity_H (k + 1) + eisensteinOmega ^ 2 * hyperbinary_eval_cube_root_of_unity_H k := by
        rw [hk_eq, hyperbinary_eval_cube_root_of_unity_H_even]
      have h2 : hyperbinary_eval_cube_root_of_unity_H (m.succ + 1) =
          eisensteinOmega * hyperbinary_eval_cube_root_of_unity_H (k + 1) := by
        have : m.succ + 1 = 2 * (k + 1) + 1 := by omega
        rw [this, hyperbinary_eval_cube_root_of_unity_H_odd]
      rw [h1, h2]
      exact hyperbinary_eval_cube_root_of_unity_valid_pair_step_even ih_k

/-- Evaluating H_m at the cube root of unity ω yields one of {0, ±1, ±ω, ±ω²}. -/
theorem hyperbinary_eval_cube_root_of_unity (m : ℕ) :
    Polynomial.aeval eisensteinOmega (hyperbinaryLengthPoly m) ∈
      ({0, 1, -1, eisensteinOmega, -eisensteinOmega, eisensteinOmega ^ 2, -eisensteinOmega ^ 2} : Set ℂ) := by
  have h := hyperbinary_eval_cube_root_of_unity_H_pair_valid m
  have h_fst := hyperbinary_eval_cube_root_of_unity_valid_pair_fst_mem h
  exact h_fst
