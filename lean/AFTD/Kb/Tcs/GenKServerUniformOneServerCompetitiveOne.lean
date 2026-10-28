import AFTD.Prelude
import AFTD.Kb.Tcs.GenKServerUniformIsRandAlg
import AFTD.Kb.Tcs.GenKServerUniformExpectedCost
import AFTD.Kb.Tcs.GenKServerUniformOpt
import AFTD.Kb.Tcs.GenKServerUniformPathCost
import AFTD.Kb.Tcs.GenKServerUniformExpectedCostFrom

/-!
# gen_k_server_uniform_one_server_competitive_one

Topic: online_algorithms   Node: 30686c476056

Provenance: helper lemma. Smallest case k = 1 of OP-613 (arXiv:2610.37192, Sec. 6): with one server the request determines the configuration, so following the requests is optimal

With one server (k = 1, configurations Fin 1 → Fin m) and any start configuration a, there are transition probabilities P with gen_k_server_uniform_is_rand_alg P whose expected cost on every request list ρ is at most gen_k_server_uniform_opt a ρ.
-/

open Finset

def gen_k_server_uniform_one_server_competitive_one_P_det {k m : ℕ} :
    List (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → (Fin k → Fin m) → ℝ :=
  fun _past r _x y => if y = r then 1 else 0

lemma gen_k_server_uniform_one_server_competitive_one_is_rand_alg (m : ℕ) :
    gen_k_server_uniform_is_rand_alg (gen_k_server_uniform_one_server_competitive_one_P_det (k := 1) (m := m)) := by
  intro past r x
  refine ⟨?_, ?_, ?_⟩
  · intro y
    dsimp [gen_k_server_uniform_one_server_competitive_one_P_det]
    split_ifs <;> linarith
  · dsimp [gen_k_server_uniform_one_server_competitive_one_P_det]
    simp only [sum_ite_eq', mem_univ, ite_true]
  · intro y hy
    dsimp [gen_k_server_uniform_one_server_competitive_one_P_det] at hy
    split_ifs at hy with h
    · subst h
      exact ⟨0, rfl⟩
    · contradiction

lemma gen_k_server_uniform_one_server_competitive_one_expected_cost_from {k m : ℕ}
    (past : List (Fin k → Fin m)) (x : Fin k → Fin m) (ρ : List (Fin k → Fin m)) :
    gen_k_server_uniform_expected_cost_from gen_k_server_uniform_one_server_competitive_one_P_det past
      (fun z => if z = x then 1 else 0) ρ =
      (gen_k_server_uniform_path_cost x ρ : ℝ) := by
  induction ρ generalizing past x with
  | nil =>
    simp [gen_k_server_uniform_expected_cost_from, gen_k_server_uniform_path_cost]
  | cons r rs ih =>
    simp only [gen_k_server_uniform_expected_cost_from, gen_k_server_uniform_path_cost]
    have h1 : (∑ x', ∑ y, (if x' = x then (1:ℝ) else 0) *
        gen_k_server_uniform_one_server_competitive_one_P_det past r x' y * (hammingDist x' y : ℝ)) =
        (hammingDist x r : ℝ) := by
      have : (fun x' => (∑ y, (if x' = x then (1:ℝ) else 0) *
          gen_k_server_uniform_one_server_competitive_one_P_det past r x' y * (hammingDist x' y : ℝ))) =
          (fun x' => if x' = x then
            (∑ y, gen_k_server_uniform_one_server_competitive_one_P_det past r x y * (hammingDist x y : ℝ))
            else 0) := by
        ext x'
        split_ifs with h
        · subst h
          simp only [one_mul]
        · simp only [zero_mul, sum_const_zero]
      rw [this, sum_ite_eq' univ x]
      simp only [mem_univ, ite_true]
      dsimp [gen_k_server_uniform_one_server_competitive_one_P_det]
      have : (fun y => (if y = r then (1:ℝ) else 0) * (hammingDist x y : ℝ)) =
          (fun y => if y = r then (hammingDist x r : ℝ) else 0) := by
        ext y
        split_ifs with h
        · subst h; ring
        · ring
      rw [this, sum_ite_eq' univ r]
      simp only [mem_univ, ite_true]
    have h2 : (fun y => ∑ x', (if x' = x then (1:ℝ) else 0) *
        gen_k_server_uniform_one_server_competitive_one_P_det past r x' y) =
        (fun y => if y = r then (1:ℝ) else 0) := by
      ext y
      have : (fun x' => (if x' = x then (1:ℝ) else 0) *
          gen_k_server_uniform_one_server_competitive_one_P_det past r x' y) =
          (fun x' => if x' = x then gen_k_server_uniform_one_server_competitive_one_P_det past r x y else 0) := by
        ext x'
        split_ifs with h
        · subst h; ring
        · ring
      rw [this, sum_ite_eq' univ x]
      simp only [mem_univ, ite_true]
      dsimp [gen_k_server_uniform_one_server_competitive_one_P_det]
    rw [h1, h2, ih (past ++ [r]) r]
    push_cast
    rfl

lemma gen_k_server_uniform_one_server_competitive_one_fin_one_eq_of_serves
    {m : ℕ} {o r : Fin 1 → Fin m} (h : ∃ i : Fin 1, o i = r i) : o = r := by
  obtain ⟨i, hi⟩ := h
  funext j
  have : j = i := Subsingleton.elim j i
  rw [this]
  exact hi

lemma gen_k_server_uniform_one_server_competitive_one_os_eq_of_forall₂_serves
    {m : ℕ} {os ρ : List (Fin 1 → Fin m)}
    (h : List.Forall₂ (fun o r => ∃ i, o i = r i) os ρ) : os = ρ := by
  induction h with
  | nil => rfl
  | cons h1 h2 ih =>
    rw [gen_k_server_uniform_one_server_competitive_one_fin_one_eq_of_serves h1, ih]

lemma gen_k_server_uniform_one_server_competitive_one_forall₂_serves_refl
    {m : ℕ} (ρ : List (Fin 1 → Fin m)) :
    List.Forall₂ (fun o r => ∃ i, o i = r i) ρ ρ := by
  induction ρ with
  | nil => exact List.Forall₂.nil
  | cons r rs ih =>
    exact List.Forall₂.cons ⟨0, rfl⟩ ih

lemma gen_k_server_uniform_one_server_competitive_one_opt_eq_path_cost
    (m : ℕ) (a : Fin 1 → Fin m) (ρ : List (Fin 1 → Fin m)) :
    gen_k_server_uniform_opt a ρ = gen_k_server_uniform_path_cost a ρ := by
  dsimp [gen_k_server_uniform_opt]
  have h_mem : gen_k_server_uniform_path_cost a ρ ∈
      {c | ∃ os, List.Forall₂ (fun o r => ∃ i, o i = r i) os ρ ∧ gen_k_server_uniform_path_cost a os = c} := by
    exact ⟨ρ, gen_k_server_uniform_one_server_competitive_one_forall₂_serves_refl ρ, rfl⟩
  apply le_antisymm
  · exact Nat.sInf_le h_mem
  · apply le_csInf ⟨_, h_mem⟩
    rintro c ⟨os, hos, rfl⟩
    rw [gen_k_server_uniform_one_server_competitive_one_os_eq_of_forall₂_serves hos]

theorem gen_k_server_uniform_one_server_competitive_one (m : ℕ) (a : Fin 1 → Fin m) :
    ∃ P, gen_k_server_uniform_is_rand_alg P ∧ ∀ ρ : List (Fin 1 → Fin m),
      gen_k_server_uniform_expected_cost P a ρ ≤ (gen_k_server_uniform_opt a ρ : ℝ) := by
  use gen_k_server_uniform_one_server_competitive_one_P_det
  refine ⟨gen_k_server_uniform_one_server_competitive_one_is_rand_alg m, ?_⟩
  intro ρ
  dsimp [gen_k_server_uniform_expected_cost]
  rw [gen_k_server_uniform_one_server_competitive_one_expected_cost_from,
      gen_k_server_uniform_one_server_competitive_one_opt_eq_path_cost]
