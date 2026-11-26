import AFTD.Prelude
import AFTD.Kb.Tcs.QutritConvolutionChoi

/-!
# qutrit_convolution_choi_eq_channel_choi

Topic: quantum   Node: 771d92fcf440

Provenance: helper lemma. Sanity lemma for the definition qutrit_convolution_choi, serving OP-2299: its entries are those of the Choi matrix of the convolution channel.

For every complex 3×3 matrix σ and all a, b, a', b' in Fin 3, the entry of qutrit_convolution_choi σ at row (a,b), column (a',b') equals (1/3) times the (b,b') entry of N_σ(|a⟩⟨a'|) = Tr_2[U (|a⟩⟨a'| ⊗ σ) U†], where U|x,y⟩ = |x+y, x+2y⟩ over F_3: explicitly (1/3) Σ_e Σ_r Σ_s U[(b,e),r] · (|a⟩⟨a'| ⊗ σ)[r,s] · U[(b',e),s], with r, s ranging over Fin 3 × Fin 3, U[(u,v),r] = 1 if (u,v) = (r.1 + r.2, r.1 + 2 r.2) and 0 otherwise, and (|a⟩⟨a'| ⊗ σ)[r,s] = (1 if r.1 = a and s.1 = a', else 0) · σ(r.2, s.2).
-/

theorem in1187_collapse (σ : Matrix (Fin 3) (Fin 3) ℂ) (a b a' b' : Fin 3) :
    (∑ e : Fin 3, ∑ r : Fin 3 × Fin 3, ∑ s : Fin 3 × Fin 3,
        (if (b, e) = (r.1 + r.2, r.1 + 2 * r.2) then (1 : ℂ) else 0) *
          ((if r.1 = a ∧ s.1 = a' then (1 : ℂ) else 0) * σ r.2 s.2) *
          (if (b', e) = (s.1 + s.2, s.1 + 2 * s.2) then (1 : ℂ) else 0)) =
    ∑ e : Fin 3, ∑ y : Fin 3, ∑ y' : Fin 3,
        if b = a + y ∧ e = a + 2 * y ∧ b' = a' + y' ∧ e = a' + 2 * y' then σ y y' else 0 := by
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a']
    · refine Finset.sum_congr rfl fun y' _ => ?_
      simp only [Prod.mk.injEq, and_self, if_true, one_mul]
      by_cases h : b = a + y ∧ e = a + 2 * y ∧ b' = a' + y' ∧ e = a' + 2 * y'
      · rw [if_pos h, if_pos ⟨h.1, h.2.1⟩, if_pos ⟨h.2.2.1, h.2.2.2⟩]; ring
      · rw [if_neg h]
        by_cases h1 : b = a + y ∧ e = a + 2 * y
        · have h2 : ¬ (b' = a' + y' ∧ e = a' + 2 * y') := fun h2 => h ⟨h1.1, h1.2, h2.1, h2.2⟩
          rw [if_neg h2]; ring
        · rw [if_neg h1]; ring
    · intro x _ hx
      refine Finset.sum_eq_zero fun y' _ => ?_
      simp [hx]
    · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun s _ => ?_
    simp [hx]
  · simp

theorem qutrit_convolution_choi_eq_channel_choi (σ : Matrix (Fin 3) (Fin 3) ℂ)
    (a b a' b' : Fin 3) :
    qutrit_convolution_choi σ (a, b) (a', b') =
      (1 / 3 : ℂ) * ∑ e : Fin 3, ∑ r : Fin 3 × Fin 3, ∑ s : Fin 3 × Fin 3,
        (if (b, e) = (r.1 + r.2, r.1 + 2 * r.2) then (1 : ℂ) else 0) *
          ((if r.1 = a ∧ s.1 = a' then (1 : ℂ) else 0) * σ r.2 s.2) *
          (if (b', e) = (s.1 + s.2, s.1 + 2 * s.2) then (1 : ℂ) else 0) := by
  rw [in1187_collapse]
  simp only [qutrit_convolution_choi, Matrix.of_apply, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [Fin.ext_iff] <;>
    (have h1 : (-1 : Fin 3) = 2 := rfl
     have h2 : (-2 : Fin 3) = 1 := rfl
     try simp only [h1, h2]
     ring)
