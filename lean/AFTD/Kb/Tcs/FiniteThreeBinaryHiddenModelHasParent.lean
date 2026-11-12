import AFTD.Prelude

/-!
# finite_three_binary_hidden_model_has_parent

Topic: quantum   Node: 9831adab597e

Provenance: helper lemma. Helper for OP-693, using the rank-four PPT source from https://arxiv.org/abs/1405.4502 and the normal-completion context https://arxiv.org/abs/0903.0090.

A finite hidden-variable model for three binary effects yields a joint positive parent, also for a subnormalized total.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
private noncomputable def in767_hiddenproof_probability_weight (p : Fin 3 → ℝ) (s : Fin 3 → Bool) : ℝ :=
  ∏ j, if s j then p j else 1-p j

private lemma in767_hiddenproof_probability_weight_nonneg (p : Fin 3 → ℝ)
    (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (s : Fin 3 → Bool) :
    0 ≤ in767_hiddenproof_probability_weight p s := by
  apply Finset.prod_nonneg
  intro j hj
  split <;> linarith [hp j]

private lemma in767_hiddenproof_probability_weight_sum (p : Fin 3 → ℝ) :
    (∑ s : Fin 3 → Bool, in767_hiddenproof_probability_weight p s) = 1 := by
  have hh := Finset.sum_prod_piFinset (ι := Fin 3) (Finset.univ : Finset Bool)
    (fun j b => if b then p j else 1-p j)
  simp only [Fintype.piFinset_univ] at hh
  simpa [in767_hiddenproof_probability_weight, Fintype.sum_bool] using hh

private lemma in767_hiddenproof_probability_weight_marginal (p : Fin 3 → ℝ) (j : Fin 3) :
    (∑ s : Fin 3 → Bool, if s j then in767_hiddenproof_probability_weight p s else 0) = p j := by
  let f : Fin 3 → Bool → ℝ := fun i b => if i=j then if b then p i else 0 else if b then p i else 1-p i
  have hprod (s : Fin 3 → Bool) : (∏ i, f i (s i)) =
      if s j then in767_hiddenproof_probability_weight p s else 0 := by
    fin_cases j <;> cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
      simp [f, in767_hiddenproof_probability_weight, Fin.prod_univ_three, h0,h1,h2]
  have hh := Finset.sum_prod_piFinset (ι := Fin 3) (Finset.univ : Finset Bool) f
  simp only [Fintype.piFinset_univ] at hh
  simp_rw [hprod] at hh
  fin_cases j <;> simp [f, Fintype.sum_bool, Fin.prod_univ_three] at hh ⊢ <;> linarith

private lemma in767_hiddenproof_hidden_model_parent
    (n m : ℕ) (Q : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (p : Fin 3 → Fin m → ℝ) (P : Matrix (Fin n) (Fin n) ℂ)
    (hQ : ∀ t, (Q t).PosSemidef) (hsum : (∑ t, Q t)=P)
    (hp : ∀ j t, 0 ≤ p j t ∧ p j t ≤ 1) :
    ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
      (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ∑ t, (p j t) • Q t := by
  let G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ := fun s =>
    ∑ t, in767_hiddenproof_probability_weight (fun j => p j t) s • Q t
  refine ⟨G, ?_, ?_, ?_⟩
  · intro s
    change (∑ t, in767_hiddenproof_probability_weight (fun j => p j t) s • Q t).PosSemidef
    have H (T : Finset (Fin m)) : (∑ t ∈ T, in767_hiddenproof_probability_weight (fun j => p j t) s • Q t).PosSemidef := by
      induction T using Finset.induction_on with
      | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
      | @insert t T ht ih =>
        rw [Finset.sum_insert ht]
        exact ((hQ t).smul (in767_hiddenproof_probability_weight_nonneg _ (fun j => hp j t) s)).add ih
    exact H Finset.univ
  · change (∑ s, ∑ t, in767_hiddenproof_probability_weight (fun j => p j t) s • Q t) = P
    rw [Finset.sum_comm]
    calc
      (∑ t, ∑ s, in767_hiddenproof_probability_weight (fun j => p j t) s • Q t) =
          ∑ t, (∑ s, in767_hiddenproof_probability_weight (fun j => p j t) s) • Q t := by simp [Finset.sum_smul]
      _ = ∑ t, Q t := by simp [in767_hiddenproof_probability_weight_sum]
      _ = P := hsum
  · intro j
    change (∑ s, if s j then (∑ t, in767_hiddenproof_probability_weight (fun k => p k t) s • Q t) else 0) = _
    have heq (s : Fin 3 → Bool) :
        (if s j then (∑ t, in767_hiddenproof_probability_weight (fun k => p k t) s • Q t) else 0) =
        ∑ t, (if s j then in767_hiddenproof_probability_weight (fun k => p k t) s else 0) • Q t := by
      cases hs : s j <;> simp [hs]
    simp_rw [heq]
    rw [Finset.sum_comm]
    calc
      (∑ t, ∑ s, (if s j then in767_hiddenproof_probability_weight (fun k => p k t) s else 0) • Q t) =
          ∑ t, (∑ s, if s j then in767_hiddenproof_probability_weight (fun k => p k t) s else 0) • Q t := by simp [Finset.sum_smul]
      _ = ∑ t, (p j t) • Q t := by simp [in767_hiddenproof_probability_weight_marginal]

private lemma in767_hiddenproof_weighted_hidden_model_parent
    (n m : ℕ) (Q : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (r : Fin m → ℝ) (p : Fin 3 → Fin m → ℝ) (P : Matrix (Fin n) (Fin n) ℂ)
    (hQ : ∀ t, (Q t).PosSemidef) (hsum : (∑ t, (r t) • Q t)=P)
    (hr : ∀ t, 0 ≤ r t) (hp : ∀ j t, 0 ≤ p j t ∧ p j t ≤ r t) :
    ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
      (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ∑ t, (p j t) • Q t := by
  let Q' : Fin m → Matrix (Fin n) (Fin n) ℂ := fun t => r t • Q t
  let p' : Fin 3 → Fin m → ℝ := fun j t => if r t=0 then 0 else p j t / r t
  have hQ' : ∀ t, (Q' t).PosSemidef := fun t => (hQ t).smul (hr t)
  have hp' : ∀ j t, 0 ≤ p' j t ∧ p' j t ≤ 1 := by
    intro j t
    by_cases h : r t=0
    · simp [p', h]
    · have hpos : 0 < r t := lt_of_le_of_ne (hr t) (Ne.symm h)
      simp only [p', h, if_false]
      exact ⟨div_nonneg (hp j t).1 (hr t), (div_le_one hpos).2 (hp j t).2⟩
  obtain ⟨G,hG,hGsum,hGmarg⟩ := in767_hiddenproof_hidden_model_parent n m Q' p' P hQ' hsum hp'
  refine ⟨G,hG,hGsum,?_⟩
  intro j
  rw [hGmarg j]
  apply Finset.sum_congr rfl
  intro t ht
  dsimp [Q',p']
  by_cases h : r t=0
  · have hpzero : p j t=0 := by have := hp j t; linarith
    simp [h,hpzero]
  · simp only [h, if_false, ← mul_smul]
    congr 1
    field_simp [h]

theorem finite_three_binary_hidden_model_has_parent :
  ∀ (n m : ℕ) (Q : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (p : Fin 3 → Fin m → ℝ) (P : Matrix (Fin n) (Fin n) ℂ),
    (∀ t, (Q t).PosSemidef) → (∑ t, Q t) = P →
    (∀ j t, 0 ≤ p j t ∧ p j t ≤ 1) →
    ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
      (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ∑ t, (p j t) • Q t := by
  intro n m Q p P hQ hsum hp
  exact in767_hiddenproof_hidden_model_parent n m Q p P hQ hsum hp
