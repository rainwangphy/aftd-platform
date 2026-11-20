import AFTD.Prelude
import AFTD.Kb.Tcs.TreelikeCpDerivation
import AFTD.Kb.Tcs.CnfSatisfiable
import AFTD.Kb.Tcs.LinIneq
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.CnfClauseToLin
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.CnfLitDecidableEq
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# treelike_cp_unsat_of_refutation

Topic: proof_complexity   Node: aee01e127e57

Provenance: formalization of a published result. Source: arXiv:2611.24548 Def 4.1

Soundness of treelike Cutting Planes refutations: if a CNF formula F over n variables has a treelike Cutting Planes refutation deriving 0 ≥ 1, then F is unsatisfiable (¬ CnfSatisfiable F).
-/

open Finset

def treelike_cp_unsat_of_refutation_bool_to_lin (b : Bool) : ℤ := if b then 1 else 0

def treelike_cp_unsat_of_refutation_lit_sat {V : Type*} (τ : V → Bool) (l : CnfLit V) : Prop :=
  match l with
  | CnfLit.pos v => τ v = true
  | CnfLit.neg v => τ v = false

lemma treelike_cp_unsat_of_refutation_sum_clause_identity {n : ℕ} (pos neg : Fin n → ℤ) (x : Fin n → ℤ) :
    (∑ j : Fin n, (pos j - neg j) * x j) - (1 - ∑ j : Fin n, neg j) =
    (∑ j : Fin n, (pos j * x j + neg j * (1 - x j))) - 1 := by
  have h1 : (∑ j : Fin n, (pos j - neg j) * x j) =
      (∑ j : Fin n, (pos j * x j - neg j * x j)) := by
    apply sum_congr rfl
    intro j _
    ring
  rw [h1, sum_sub_distrib]
  have h2 : (∑ j : Fin n, (pos j * x j + neg j * (1 - x j))) =
      (∑ j : Fin n, pos j * x j) + (∑ j : Fin n, (neg j * (1 - x j))) := by
    rw [sum_add_distrib]
  rw [h2]
  have h3 : (∑ j : Fin n, neg j * (1 - x j)) =
      (∑ j : Fin n, (neg j - neg j * x j)) := by
    apply sum_congr rfl
    intro j _
    ring
  rw [h3, sum_sub_distrib]
  ring

lemma treelike_cp_unsat_of_refutation_clause_term_nonneg {n : ℕ} (C : Finset (CnfLit (Fin n))) (τ : Fin n → Bool) (j : Fin n) :
    0 ≤ (if CnfLit.pos j ∈ C then (1 : ℤ) else 0) * treelike_cp_unsat_of_refutation_bool_to_lin (τ j) +
        (if CnfLit.neg j ∈ C then (1 : ℤ) else 0) * (1 - treelike_cp_unsat_of_refutation_bool_to_lin (τ j)) := by
  have h1 : 0 ≤ treelike_cp_unsat_of_refutation_bool_to_lin (τ j) := by cases τ j <;> decide
  have h2 : 0 ≤ 1 - treelike_cp_unsat_of_refutation_bool_to_lin (τ j) := by cases τ j <;> decide
  have hpos : 0 ≤ (if CnfLit.pos j ∈ C then (1 : ℤ) else 0) := by split_ifs <;> omega
  have hneg : 0 ≤ (if CnfLit.neg j ∈ C then (1 : ℤ) else 0) := by split_ifs <;> omega
  nlinarith

lemma treelike_cp_unsat_of_refutation_clause_term_ge_one {n : ℕ} (C : Finset (CnfLit (Fin n))) (τ : Fin n → Bool)
    (l : CnfLit (Fin n)) (hl : l ∈ C) (hsat : treelike_cp_unsat_of_refutation_lit_sat τ l) :
    1 ≤ ∑ j : Fin n, ((if CnfLit.pos j ∈ C then (1 : ℤ) else 0) * treelike_cp_unsat_of_refutation_bool_to_lin (τ j) +
        (if CnfLit.neg j ∈ C then (1 : ℤ) else 0) * (1 - treelike_cp_unsat_of_refutation_bool_to_lin (τ j))) := by
  cases l with
  | pos v =>
    have hv_term : 1 ≤ (if CnfLit.pos v ∈ C then (1 : ℤ) else 0) * treelike_cp_unsat_of_refutation_bool_to_lin (τ v) +
        (if CnfLit.neg v ∈ C then (1 : ℤ) else 0) * (1 - treelike_cp_unsat_of_refutation_bool_to_lin (τ v)) := by
      have hpos : (if CnfLit.pos v ∈ C then (1 : ℤ) else 0) = 1 := if_pos hl
      have htau : treelike_cp_unsat_of_refutation_bool_to_lin (τ v) = 1 := by simp [treelike_cp_unsat_of_refutation_bool_to_lin, treelike_cp_unsat_of_refutation_lit_sat] at *; exact hsat
      have hneg_nonneg : 0 ≤ (if CnfLit.neg v ∈ C then (1 : ℤ) else 0) * (1 - treelike_cp_unsat_of_refutation_bool_to_lin (τ v)) := by
        have hneg : 0 ≤ (if CnfLit.neg v ∈ C then (1 : ℤ) else 0) := by split_ifs <;> omega
        have h2 : 0 ≤ 1 - treelike_cp_unsat_of_refutation_bool_to_lin (τ v) := by cases τ v <;> decide
        nlinarith
      rw [hpos, htau]
      linarith
    have hsum := Finset.single_le_sum (f := fun j => (if CnfLit.pos j ∈ C then (1 : ℤ) else 0) * treelike_cp_unsat_of_refutation_bool_to_lin (τ j) +
        (if CnfLit.neg j ∈ C then (1 : ℤ) else 0) * (1 - treelike_cp_unsat_of_refutation_bool_to_lin (τ j)))
      (fun j _ => treelike_cp_unsat_of_refutation_clause_term_nonneg C τ j) (Finset.mem_univ v)
    linarith
  | neg v =>
    have hv_term : 1 ≤ (if CnfLit.pos v ∈ C then (1 : ℤ) else 0) * treelike_cp_unsat_of_refutation_bool_to_lin (τ v) +
        (if CnfLit.neg v ∈ C then (1 : ℤ) else 0) * (1 - treelike_cp_unsat_of_refutation_bool_to_lin (τ v)) := by
      have hneg : (if CnfLit.neg v ∈ C then (1 : ℤ) else 0) = 1 := if_pos hl
      have htau : 1 - treelike_cp_unsat_of_refutation_bool_to_lin (τ v) = 1 := by
        have : τ v = false := hsat
        simp [treelike_cp_unsat_of_refutation_bool_to_lin, this]
      have hpos_nonneg : 0 ≤ (if CnfLit.pos v ∈ C then (1 : ℤ) else 0) * treelike_cp_unsat_of_refutation_bool_to_lin (τ v) := by
        have hpos : 0 ≤ (if CnfLit.pos v ∈ C then (1 : ℤ) else 0) := by split_ifs <;> omega
        have h1 : 0 ≤ treelike_cp_unsat_of_refutation_bool_to_lin (τ v) := by cases τ v <;> decide
        nlinarith
      rw [hneg, htau]
      linarith
    have hsum := Finset.single_le_sum (f := fun j => (if CnfLit.pos j ∈ C then (1 : ℤ) else 0) * treelike_cp_unsat_of_refutation_bool_to_lin (τ j) +
        (if CnfLit.neg j ∈ C then (1 : ℤ) else 0) * (1 - treelike_cp_unsat_of_refutation_bool_to_lin (τ j)))
      (fun j _ => treelike_cp_unsat_of_refutation_clause_term_nonneg C τ j) (Finset.mem_univ v)
    linarith

lemma treelike_cp_unsat_of_refutation_clause_sound {n : ℕ} (C : Finset (CnfLit (Fin n))) (τ : Fin n → Bool)
    (l : CnfLit (Fin n)) (hl : l ∈ C) (hsat : treelike_cp_unsat_of_refutation_lit_sat τ l) :
    (cnf_clause_to_lin n C).const ≤ ∑ j : Fin n, (cnf_clause_to_lin n C).coeffs j * treelike_cp_unsat_of_refutation_bool_to_lin (τ j) := by
  dsimp [cnf_clause_to_lin]
  have hid := treelike_cp_unsat_of_refutation_sum_clause_identity (fun j => if CnfLit.pos j ∈ C then 1 else 0)
    (fun j => if CnfLit.neg j ∈ C then 1 else 0) (fun j => treelike_cp_unsat_of_refutation_bool_to_lin (τ j))
  have hge := treelike_cp_unsat_of_refutation_clause_term_ge_one C τ l hl hsat
  linarith

lemma treelike_cp_unsat_of_refutation_div_rule_sound (L_const : ℤ) (c_sum : ℤ) (α : ℕ) (hα : 0 < α)
    (hineq : L_const ≤ α * c_sum) :
    ⌈(L_const : ℚ) / (α : ℚ)⌉ ≤ c_sum := by
  rw [Int.ceil_le]
  have hα_pos : 0 < (α : ℚ) := by positivity
  rw [div_le_iff₀ hα_pos]
  have hineq_q : (L_const : ℚ) ≤ (c_sum : ℚ) * (α : ℚ) := by
    exact_mod_cast (by linarith : L_const ≤ c_sum * α)
  linarith

lemma treelike_cp_unsat_of_refutation_sum_mul_factor {n : ℕ} (α : ℕ) (c : Fin n → ℤ) (x : Fin n → ℤ) :
    (∑ j : Fin n, (↑α * c j) * x j) = ↑α * (∑ j : Fin n, c j * x j) := by
  have : (fun j => (↑α * c j) * x j) = (fun j => ↑α * (c j * x j)) := by
    funext j
    ring
  rw [this, mul_sum]

lemma treelike_cp_unsat_of_refutation_division_step_sound {n : ℕ} (L : LinIneq n) (c : Fin n → ℤ) (α : ℕ) (hα : 0 < α)
    (hdiv : ∀ j, L.coeffs j = ↑α * c j) (τ : Fin n → Bool)
    (ih : L.const ≤ ∑ j : Fin n, L.coeffs j * treelike_cp_unsat_of_refutation_bool_to_lin (τ j)) :
    ⌈(L.const : ℚ) / (α : ℚ)⌉ ≤ ∑ j : Fin n, c j * treelike_cp_unsat_of_refutation_bool_to_lin (τ j) := by
  have h_sum : (∑ j : Fin n, L.coeffs j * treelike_cp_unsat_of_refutation_bool_to_lin (τ j)) =
      ↑α * (∑ j : Fin n, c j * treelike_cp_unsat_of_refutation_bool_to_lin (τ j)) := by
    have h_coeff : (fun j => L.coeffs j * treelike_cp_unsat_of_refutation_bool_to_lin (τ j)) =
        (fun j => (↑α * c j) * treelike_cp_unsat_of_refutation_bool_to_lin (τ j)) := by
      funext j
      rw [hdiv j]
    rw [h_coeff, treelike_cp_unsat_of_refutation_sum_mul_factor]
  have hineq : L.const ≤ ↑α * (∑ j : Fin n, c j * treelike_cp_unsat_of_refutation_bool_to_lin (τ j)) := by
    linarith [ih, h_sum]
  exact treelike_cp_unsat_of_refutation_div_rule_sound L.const (∑ j : Fin n, c j * treelike_cp_unsat_of_refutation_bool_to_lin (τ j)) α hα hineq

lemma treelike_cp_unsat_of_refutation_lin_comb_sound {n : ℕ} (lam1 lam2 : ℕ) (L1 L2 : LinIneq n) (x : Fin n → ℤ)
    (h1 : L1.const ≤ ∑ j : Fin n, L1.coeffs j * x j)
    (h2 : L2.const ≤ ∑ j : Fin n, L2.coeffs j * x j) :
    (↑lam1 * L1.const + ↑lam2 * L2.const) ≤
      ∑ j : Fin n, (↑lam1 * L1.coeffs j + ↑lam2 * L2.coeffs j) * x j := by
  have h_split : (∑ j : Fin n, (↑lam1 * L1.coeffs j + ↑lam2 * L2.coeffs j) * x j) =
      ↑lam1 * (∑ j : Fin n, L1.coeffs j * x j) + ↑lam2 * (∑ j : Fin n, L2.coeffs j * x j) := by
    have : (fun j => (↑lam1 * L1.coeffs j + ↑lam2 * L2.coeffs j) * x j) =
        (fun j => ↑lam1 * (L1.coeffs j * x j) + ↑lam2 * (L2.coeffs j * x j)) := by
      funext j; ring
    rw [this, sum_add_distrib, mul_sum, mul_sum]
  rw [h_split]
  have h_lam1 : 0 ≤ (lam1 : ℤ) := by positivity
  have h_lam2 : 0 ≤ (lam2 : ℤ) := by positivity
  nlinarith

lemma treelike_cp_unsat_of_refutation_sound (n : ℕ) (F : List (List (CnfLit (Fin n)))) (τ : Fin n → Bool)
    (hτ : ∀ c ∈ F, ∃ l ∈ c, treelike_cp_unsat_of_refutation_lit_sat τ l)
    {L : LinIneq n} (d : TreelikeCpDerivation n F L) :
    L.const ≤ ∑ j : Fin n, L.coeffs j * treelike_cp_unsat_of_refutation_bool_to_lin (τ j) := by
  induction d with
  | trivial =>
    simp
  | box_lower i =>
    have : (fun j => (if j = i then (1 : ℤ) else 0) * treelike_cp_unsat_of_refutation_bool_to_lin (τ j)) =
        (fun j => if j = i then treelike_cp_unsat_of_refutation_bool_to_lin (τ j) else 0) := by
      funext j
      split_ifs <;> ring
    rw [this]
    simp
    cases τ i <;> decide
  | box_upper i =>
    have : (fun j => (if j = i then (-1 : ℤ) else 0) * treelike_cp_unsat_of_refutation_bool_to_lin (τ j)) =
        (fun j => if j = i then -treelike_cp_unsat_of_refutation_bool_to_lin (τ j) else 0) := by
      funext j
      split_ifs <;> ring
    rw [this]
    simp
    cases τ i <;> decide
  | clause C hC =>
    obtain ⟨l, hl, hsat⟩ := hτ C hC
    exact treelike_cp_unsat_of_refutation_clause_sound C.toFinset τ l (List.mem_toFinset.mpr hl) hsat
  | lin_comb d1 d2 lam1 lam2 ih1 ih2 =>
    exact treelike_cp_unsat_of_refutation_lin_comb_sound lam1 lam2 _ _ (fun j => treelike_cp_unsat_of_refutation_bool_to_lin (τ j)) ih1 ih2
  | division d c α hα hdiv ih =>
    exact treelike_cp_unsat_of_refutation_division_step_sound _ c α hα hdiv τ ih

/-- Soundness of treelike Cutting Planes refutations. -/
theorem treelike_cp_unsat_of_refutation (n : ℕ) (F : List (List (CnfLit (Fin n)))) (d : TreelikeCpDerivation n F { coeffs := fun _ => 0, const := 1 }) : ¬ CnfSatisfiable F := by
  intro ⟨τ, hτ⟩
  have hτ' : ∀ c ∈ F, ∃ l ∈ c, treelike_cp_unsat_of_refutation_lit_sat τ l := by
    intro c hc
    obtain ⟨l, hl, hsat⟩ := hτ c hc
    exact ⟨l, hl, hsat⟩
  have hsound := treelike_cp_unsat_of_refutation_sound n F τ hτ' d
  dsimp at hsound
  simp at hsound
