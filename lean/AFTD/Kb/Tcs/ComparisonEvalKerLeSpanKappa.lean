import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonEvalMatrix
import AFTD.Kb.Tcs.ComparisonTriangleKappa
import AFTD.Kb.Tcs.ComparisonPhi1LinearIndependent
import AFTD.Kb.Tcs.ComparisonPhi2
import AFTD.Kb.Tcs.ComparisonFeature2
import AFTD.Kb.Tcs.ComparisonTriangleKappaMemEvalKer
import AFTD.Kb.Tcs.ComparisonSign
import AFTD.Kb.Tcs.ComparisonPhi1
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.ComparisonEdge
import AFTD.Kb.Tcs.ComparisonFeature1
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.ComparisonTriangle

/-!
# comparison_eval_ker_le_span_kappa

Topic: quantum   Node: b71deb9b33bb

Provenance: helper lemma. Step of arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, Lemma 1 (quadratic_comparison_evaluation_kernel_and_projector)

Every formal quadratic feature vector c in F_2 that evaluates to zero on every strict order (<phi_2(x), c> = 0 for all permutations x of Fin n) is a linear combination of the triangle relation vectors kappa_abc.
-/

theorem cmp_finset_pair_eq_pair {α : Type*} [DecidableEq α] (p q r s : α) :
    ({p, q} : Finset α) = {r, s} ↔ (p = r ∧ q = s) ∨ (p = s ∧ q = r) := by
  rw [← Finset.coe_inj, Finset.coe_pair, Finset.coe_pair, Set.pair_eq_pair_iff]

def cmp_eAB {n : ℕ} (t : comparison_triangle n) : comparison_edge n := ⟨(t.1.1, t.1.2.1), t.2.1⟩
def cmp_eAC {n : ℕ} (t : comparison_triangle n) : comparison_edge n :=
  ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩
def cmp_eBC {n : ℕ} (t : comparison_triangle n) : comparison_edge n := ⟨(t.1.2.1, t.1.2.2), t.2.2⟩

theorem cmp_eAB_ne_eAC {n : ℕ} (t : comparison_triangle n) : cmp_eAB t ≠ cmp_eAC t :=
  fun h => (ne_of_lt t.2.2) (congrArg (fun p : comparison_edge n => p.1.2) h)
theorem cmp_eAB_ne_eBC {n : ℕ} (t : comparison_triangle n) : cmp_eAB t ≠ cmp_eBC t :=
  fun h => (ne_of_lt t.2.1) (congrArg (fun p : comparison_edge n => p.1.1) h)
theorem cmp_eAC_ne_eBC {n : ℕ} (t : comparison_triangle n) : cmp_eAC t ≠ cmp_eBC t :=
  fun h => (ne_of_lt t.2.1) (congrArg (fun p : comparison_edge n => p.1.1) h)

def cmp_qA {n : ℕ} (t : comparison_triangle n) : comparison_feature2 n :=
  Sum.inr ⟨{cmp_eAB t, cmp_eAC t}, Finset.card_pair (cmp_eAB_ne_eAC t)⟩
def cmp_qB {n : ℕ} (t : comparison_triangle n) : comparison_feature2 n :=
  Sum.inr ⟨{cmp_eAB t, cmp_eBC t}, Finset.card_pair (cmp_eAB_ne_eBC t)⟩
def cmp_qC {n : ℕ} (t : comparison_triangle n) : comparison_feature2 n :=
  Sum.inr ⟨{cmp_eAC t, cmp_eBC t}, Finset.card_pair (cmp_eAC_ne_eBC t)⟩

theorem cmp_kappa_eq {n : ℕ} (t : comparison_triangle n) :
    comparison_triangle_kappa t = fun i => ((if i = cmp_qA t then 1 else 0) -
      (if i = cmp_qB t then 1 else 0) + (if i = cmp_qC t then 1 else 0) -
      (if i = (Sum.inl none : comparison_feature2 n) then 1 else 0) : ℝ) := rfl

section
variable {n : ℕ}

theorem cmp_qA_inj (t t' : comparison_triangle n) : cmp_qA t = cmp_qA t' ↔ t = t' := by
  constructor
  · intro h
    obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
    obtain ⟨⟨a', b', c'⟩, hab', hbc'⟩ := t'
    simp only [Fin.lt_def] at hab hbc hab' hbc'
    simp only [cmp_qA, Sum.inr.injEq, Subtype.mk.injEq, cmp_finset_pair_eq_pair,
      cmp_eAB, cmp_eAC, Prod.mk.injEq, Fin.ext_iff] at h
    simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff]
    omega
  · rintro rfl; rfl

theorem cmp_qB_inj (t t' : comparison_triangle n) : cmp_qB t = cmp_qB t' ↔ t = t' := by
  constructor
  · intro h
    obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
    obtain ⟨⟨a', b', c'⟩, hab', hbc'⟩ := t'
    simp only [Fin.lt_def] at hab hbc hab' hbc'
    simp only [cmp_qB, Sum.inr.injEq, Subtype.mk.injEq, cmp_finset_pair_eq_pair,
      cmp_eAB, cmp_eBC, Prod.mk.injEq, Fin.ext_iff] at h
    simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff]
    omega
  · rintro rfl; rfl

theorem cmp_qC_inj (t t' : comparison_triangle n) : cmp_qC t = cmp_qC t' ↔ t = t' := by
  constructor
  · intro h
    obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
    obtain ⟨⟨a', b', c'⟩, hab', hbc'⟩ := t'
    simp only [Fin.lt_def] at hab hbc hab' hbc'
    simp only [cmp_qC, Sum.inr.injEq, Subtype.mk.injEq, cmp_finset_pair_eq_pair,
      cmp_eAC, cmp_eBC, Prod.mk.injEq, Fin.ext_iff] at h
    simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff]
    omega
  · rintro rfl; rfl

theorem cmp_qA_ne_qB (t t' : comparison_triangle n) : cmp_qA t ≠ cmp_qB t' := by
  intro h; revert h
  obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
  obtain ⟨⟨a', b', c'⟩, hab', hbc'⟩ := t'
  simp only [Fin.lt_def] at hab hbc hab' hbc'
  simp only [cmp_qA, cmp_qB, cmp_qC, Sum.inr.injEq, Subtype.mk.injEq, cmp_finset_pair_eq_pair,
    cmp_eAB, cmp_eAC, cmp_eBC, Prod.mk.injEq, Fin.ext_iff]
  omega
theorem cmp_qA_ne_qC (t t' : comparison_triangle n) : cmp_qA t ≠ cmp_qC t' := by
  intro h; revert h
  obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
  obtain ⟨⟨a', b', c'⟩, hab', hbc'⟩ := t'
  simp only [Fin.lt_def] at hab hbc hab' hbc'
  simp only [cmp_qA, cmp_qB, cmp_qC, Sum.inr.injEq, Subtype.mk.injEq, cmp_finset_pair_eq_pair,
    cmp_eAB, cmp_eAC, cmp_eBC, Prod.mk.injEq, Fin.ext_iff]
  omega
theorem cmp_qB_ne_qC (t t' : comparison_triangle n) : cmp_qB t ≠ cmp_qC t' := by
  intro h; revert h
  obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
  obtain ⟨⟨a', b', c'⟩, hab', hbc'⟩ := t'
  simp only [Fin.lt_def] at hab hbc hab' hbc'
  simp only [cmp_qA, cmp_qB, cmp_qC, Sum.inr.injEq, Subtype.mk.injEq, cmp_finset_pair_eq_pair,
    cmp_eAB, cmp_eAC, cmp_eBC, Prod.mk.injEq, Fin.ext_iff]
  omega
theorem cmp_qB_ne_qA (t t' : comparison_triangle n) : cmp_qB t ≠ cmp_qA t' :=
  fun h => cmp_qA_ne_qB t' t h.symm
theorem cmp_qC_ne_qA (t t' : comparison_triangle n) : cmp_qC t ≠ cmp_qA t' :=
  fun h => cmp_qA_ne_qC t' t h.symm
theorem cmp_qC_ne_qB (t t' : comparison_triangle n) : cmp_qC t ≠ cmp_qB t' :=
  fun h => cmp_qB_ne_qC t' t h.symm
theorem cmp_qA_ne_O (t : comparison_triangle n) : cmp_qA t ≠ Sum.inl none := by
  simp [cmp_qA]
theorem cmp_qB_ne_O (t : comparison_triangle n) : cmp_qB t ≠ Sum.inl none := by
  simp [cmp_qB]
theorem cmp_qC_ne_O (t : comparison_triangle n) : cmp_qC t ≠ Sum.inl none := by
  simp [cmp_qC]
theorem cmp_O_ne_qA (t : comparison_triangle n) : (Sum.inl none : comparison_feature2 n) ≠ cmp_qA t :=
  (cmp_qA_ne_O t).symm
theorem cmp_O_ne_qB (t : comparison_triangle n) : (Sum.inl none : comparison_feature2 n) ≠ cmp_qB t :=
  (cmp_qB_ne_O t).symm
theorem cmp_O_ne_qC (t : comparison_triangle n) : (Sum.inl none : comparison_feature2 n) ≠ cmp_qC t :=
  (cmp_qC_ne_O t).symm

theorem cmp_kappa_qA (t t' : comparison_triangle n) :
    comparison_triangle_kappa t' (cmp_qA t) = if t = t' then 1 else 0 := by
  rw [cmp_kappa_eq]
  simp only [cmp_qA_inj, cmp_qA_ne_qB, cmp_qA_ne_qC, cmp_qA_ne_O, if_false]
  ring

end



section
variable {n : ℕ}

theorem cmp_ker_eval {c : comparison_feature2 n → ℝ}
    (hc : c ∈ LinearMap.ker (comparison_eval_matrix n).mulVecLin) (x : Equiv.Perm (Fin n)) :
    ∑ i, comparison_phi2 x i * c i = 0 := by
  have := congrFun (LinearMap.mem_ker.mp hc) x
  simpa [Matrix.mulVec, dotProduct, comparison_eval_matrix] using this

theorem cmp_sign_rev (x : Equiv.Perm (Fin n)) (e : comparison_edge n) :
    comparison_sign (x.trans Fin.revPerm) e = - comparison_sign x e := by
  obtain ⟨⟨a, b⟩, hab⟩ := e
  have hne : x a ≠ x b := fun h => (ne_of_lt hab) (x.injective h)
  simp only [comparison_sign, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_lt_rev]
  rw [Ne, Fin.ext_iff] at hne
  simp only [Fin.lt_def] at *
  split_ifs <;> (try norm_num) <;> omega

theorem cmp_lin_zero {c : comparison_feature2 n → ℝ}
    (hc : ∀ x : Equiv.Perm (Fin n), ∑ i, comparison_phi2 x i * c i = 0) (e : comparison_edge n) :
    c (Sum.inl (some e)) = 0 := by
  classical
  have key : ∀ x : Equiv.Perm (Fin n),
      ∑ e : comparison_edge n, c (Sum.inl (some e)) * comparison_sign x e = 0 := by
    intro x
    have h1 := hc x
    have h2 := hc (x.trans Fin.revPerm)
    simp only [Fintype.sum_sum_type, Fintype.sum_option, comparison_phi2, comparison_phi1] at h1 h2
    have hq : ∀ s : {s : Finset (comparison_edge n) // s.card = 2},
        ∏ e ∈ s.1, -comparison_sign x e = ∏ e ∈ s.1, comparison_sign x e := by
      intro s
      simp only [Finset.prod_neg, s.2]
      norm_num
    simp only [cmp_sign_rev, neg_mul, Finset.sum_neg_distrib, hq] at h2
    have : ∑ e, comparison_sign x e * c (Sum.inl (some e)) = 0 := by linarith
    simpa [mul_comm] using this
  have hli := comparison_phi1_linearIndependent n
  rw [Fintype.linearIndependent_iff] at hli
  have := hli (fun i => match i with | none => 0 | some e => c (Sum.inl (some e))) (by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_option, comparison_phi1,
      zero_mul, zero_add, Pi.zero_apply]
    exact key x)
  exact this (some e)

theorem cmp_exists_perm3 (a b d : Fin n) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (h3 : 3 ≤ n) :
    ∃ x : Equiv.Perm (Fin n), (x a).val = 0 ∧ (x b).val = 1 ∧ (x d).val = 2 := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ![a, b, d]
    (fun i : Fin 3 => (⟨i.val, by have := i.isLt; omega⟩ : Fin n))
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [eq_comm])
    (by intro i j h; simpa [Fin.ext_iff] using h)
  refine ⟨σ, ?_, ?_, ?_⟩
  · simpa using congrArg Fin.val (hσ 0)
  · simpa using congrArg Fin.val (hσ 1)
  · simpa using congrArg Fin.val (hσ 2)

theorem cmp_exists_perm4 (a b d f : Fin n) (hab : a ≠ b) (had : a ≠ d) (haf : a ≠ f)
    (hbd : b ≠ d) (hbf : b ≠ f) (hdf : d ≠ f) (h4 : 4 ≤ n) :
    ∃ x : Equiv.Perm (Fin n), (x a).val = 0 ∧ (x b).val = 1 ∧ (x d).val = 2 ∧ (x f).val = 3 := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ![a, b, d, f]
    (fun i : Fin 4 => (⟨i.val, by have := i.isLt; omega⟩ : Fin n))
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [eq_comm])
    (by intro i j h; simpa [Fin.ext_iff] using h)
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Fin.val (hσ 0)
  · simpa using congrArg Fin.val (hσ 1)
  · simpa using congrArg Fin.val (hσ 2)
  · simpa using congrArg Fin.val (hσ 3)

theorem cmp_block_preserve (β : Fin n → ℕ) (hβ : Monotone β) (ρ : Equiv.Perm (Fin n))
    (hρ : ∀ k, β (ρ k) = β k) (i j : Fin n) (hij : β i ≠ β j) : (ρ i < ρ j ↔ i < j) := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have h1 := hβ h'
    have h2 := hβ h.le
    rw [hρ, hρ] at h2
    omega
  · intro h
    by_contra h'
    push Not at h'
    have h1 := hβ h'
    rw [hρ, hρ] at h1
    have h2 := hβ h.le
    omega

theorem cmp_sign_block (β : Fin n → ℕ) (hβ : Monotone β) (ρ : Equiv.Perm (Fin n))
    (hρ : ∀ k, β (ρ k) = β k) (x : Equiv.Perm (Fin n)) (e : comparison_edge n)
    (he : β (x e.1.1) ≠ β (x e.1.2)) :
    comparison_sign (x.trans ρ) e = comparison_sign x e := by
  simp only [comparison_sign, Equiv.trans_apply, cmp_block_preserve β hβ ρ hρ _ _ he]

theorem cmp_swap_block (β : Fin n → ℕ) (i j : Fin n) (h : β i = β j) (k : Fin n) :
    β (Equiv.swap i j k) = β k := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

end

section
variable {n : ℕ}

theorem cmp_eAC_ne_eAB (t : comparison_triangle n) : cmp_eAC t ≠ cmp_eAB t :=
  (cmp_eAB_ne_eAC t).symm
theorem cmp_eBC_ne_eAB (t : comparison_triangle n) : cmp_eBC t ≠ cmp_eAB t :=
  (cmp_eAB_ne_eBC t).symm
theorem cmp_eBC_ne_eAC (t : comparison_triangle n) : cmp_eBC t ≠ cmp_eAC t :=
  (cmp_eAC_ne_eBC t).symm

theorem cmp_edge_in_tri (t : comparison_triangle n) (x0 : Equiv.Perm (Fin n))
    (h0 : (x0 t.1.1).val = 0) (h1 : (x0 t.1.2.1).val = 1) (h2 : (x0 t.1.2.2).val = 2)
    (e : comparison_edge n) (he1 : (x0 e.1.1).val < 3) (he2 : (x0 e.1.2).val < 3) :
    e = cmp_eAB t ∨ e = cmp_eAC t ∨ e = cmp_eBC t := by
  have hl : ∀ v : Fin n, (x0 v).val < 3 → v = t.1.1 ∨ v = t.1.2.1 ∨ v = t.1.2.2 := by
    intro v hv
    have : (x0 v).val = 0 ∨ (x0 v).val = 1 ∨ (x0 v).val = 2 := by omega
    rcases this with h | h | h
    · left; exact x0.injective (Fin.ext (h.trans h0.symm))
    · right; left; exact x0.injective (Fin.ext (h.trans h1.symm))
    · right; right; exact x0.injective (Fin.ext (h.trans h2.symm))
  have hab : t.1.1 < t.1.2.1 := t.2.1
  have hbd : t.1.2.1 < t.1.2.2 := t.2.2
  obtain ⟨⟨e1, e2⟩, he⟩ := e
  have he' : e1 < e2 := he
  simp only [Fin.lt_def] at hab hbd he'
  simp only [cmp_eAB, cmp_eAC, cmp_eBC, Subtype.mk.injEq, Prod.mk.injEq]
  rcases hl e1 he1 with h | h | h <;> rcases hl e2 he2 with h' | h' | h' <;> subst h h' <;>
    first | (left; exact ⟨rfl, rfl⟩) | (right; left; exact ⟨rfl, rfl⟩) |
      (right; right; exact ⟨rfl, rfl⟩) | (exfalso; omega)

def cmp_beta3 (k : Fin n) : ℕ := if k.val < 3 then 0 else k.val

theorem cmp_beta3_mono : Monotone (cmp_beta3 (n := n)) := by
  intro i j h
  simp only [cmp_beta3]
  rw [Fin.le_def] at h
  split_ifs <;> omega

theorem cmp_tri_sign_cases (t : comparison_triangle n) (x0 : Equiv.Perm (Fin n))
    (h0 : (x0 t.1.1).val = 0) (h1 : (x0 t.1.2.1).val = 1) (h2 : (x0 t.1.2.2).val = 2)
    (ρ : Equiv.Perm (Fin n)) (hρ : ∀ k, cmp_beta3 (ρ k) = cmp_beta3 k) (e : comparison_edge n) :
    comparison_sign (x0.trans ρ) e =
      if e = cmp_eAB t then (if ρ (x0 t.1.1) < ρ (x0 t.1.2.1) then 1 else -1)
      else if e = cmp_eAC t then (if ρ (x0 t.1.1) < ρ (x0 t.1.2.2) then 1 else -1)
      else if e = cmp_eBC t then (if ρ (x0 t.1.2.1) < ρ (x0 t.1.2.2) then 1 else -1)
      else comparison_sign x0 e := by
  by_cases g1 : e = cmp_eAB t
  · rw [if_pos g1, g1]; rfl
  rw [if_neg g1]
  by_cases g2 : e = cmp_eAC t
  · rw [if_pos g2, g2]; rfl
  rw [if_neg g2]
  by_cases g3 : e = cmp_eBC t
  · rw [if_pos g3, g3]; rfl
  rw [if_neg g3]
  apply cmp_sign_block cmp_beta3 cmp_beta3_mono ρ hρ
  intro hb
  have hne : (x0 e.1.1).val ≠ (x0 e.1.2).val := fun h' =>
    (ne_of_lt e.2) (x0.injective (Fin.ext h'))
  simp only [cmp_beta3] at hb
  have hlt : (x0 e.1.1).val < 3 ∧ (x0 e.1.2).val < 3 := by split_ifs at hb <;> omega
  rcases cmp_edge_in_tri t x0 h0 h1 h2 e hlt.1 hlt.2 with h' | h' | h'
  exacts [g1 h', g2 h', g3 h']

theorem cmp_edge_cases (t : comparison_triangle n) (g : comparison_edge n) :
    g = cmp_eAB t ∨ g = cmp_eAC t ∨ g = cmp_eBC t ∨
      (g ≠ cmp_eAB t ∧ g ≠ cmp_eAC t ∧ g ≠ cmp_eBC t) := by
  by_cases h1 : g = cmp_eAB t
  · exact Or.inl h1
  by_cases h2 : g = cmp_eAC t
  · exact Or.inr (Or.inl h2)
  by_cases h3 : g = cmp_eBC t
  · exact Or.inr (Or.inr (Or.inl h3))
  exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩))

theorem cmp_comb4 {c : comparison_feature2 n → ℝ}
    (hc : ∀ x : Equiv.Perm (Fin n), ∑ i, comparison_phi2 x i * c i = 0)
    (y0 y1 y2 y3 : Equiv.Perm (Fin n)) (K : comparison_feature2 n → ℝ)
    (hK : ∀ i, comparison_phi2 y0 i + comparison_phi2 y1 i - comparison_phi2 y2 i -
      comparison_phi2 y3 i = K i) :
    ∑ i, K i * c i = 0 := by
  simp only [← hK, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, hc]
  ring

theorem cmp_tri_rel {c : comparison_feature2 n → ℝ}
    (hc : ∀ x : Equiv.Perm (Fin n), ∑ i, comparison_phi2 x i * c i = 0)
    (t : comparison_triangle n) :
    c (cmp_qA t) + c (cmp_qB t) = 0 ∧ c (cmp_qB t) + c (cmp_qC t) = 0 := by
  classical
  have hab : t.1.1 < t.1.2.1 := t.2.1
  have hbd : t.1.2.1 < t.1.2.2 := t.2.2
  have h3 : 3 ≤ n := by
    have := t.1.2.2.isLt; simp only [Fin.lt_def] at hab hbd; omega
  obtain ⟨x0, h0, h1, h2⟩ := cmp_exists_perm3 t.1.1 t.1.2.1 t.1.2.2 (ne_of_lt hab)
    (ne_of_lt (hab.trans hbd)) (ne_of_lt hbd) h3
  set r0 : Fin n := ⟨0, by omega⟩ with hr0
  set r1 : Fin n := ⟨1, by omega⟩ with hr1
  set r2 : Fin n := ⟨2, by omega⟩ with hr2
  have ha : x0 t.1.1 = r0 := Fin.ext h0
  have hb : x0 t.1.2.1 = r1 := Fin.ext h1
  have hd : x0 t.1.2.2 = r2 := Fin.ext h2
  have hb01 : cmp_beta3 r0 = cmp_beta3 r1 := by simp [cmp_beta3, r0, r1]
  have hb02 : cmp_beta3 r0 = cmp_beta3 r2 := by simp [cmp_beta3, r0, r2]
  have hb12 : cmp_beta3 r1 = cmp_beta3 r2 := by simp [cmp_beta3, r1, r2]
  have hn01 : r0 ≠ r1 := by simp [r0, r1]
  have hn02 : r0 ≠ r2 := by simp [r0, r2]
  have hn12 : r1 ≠ r2 := by simp [r1, r2]
  have l01 : r0 < r1 := by simp [r0, r1, Fin.lt_def]
  have l02 : r0 < r2 := by simp [r0, r2, Fin.lt_def]
  have l12 : r1 < r2 := by simp [r1, r2, Fin.lt_def]
  have hS := cmp_tri_sign_cases t x0 h0 h1 h2
  -- the five rank permutations
  have T0 : ∀ e, comparison_sign (x0.trans 1) e = if e = cmp_eAB t then 1
      else if e = cmp_eAC t then 1 else if e = cmp_eBC t then 1 else comparison_sign x0 e := by
    intro e; rw [hS 1 (fun k => rfl) e]
    simp [ha, hb, hd, l01, l02, l12]
  have T1 : ∀ e, comparison_sign (x0.trans (Equiv.swap r0 r2)) e = if e = cmp_eAB t then -1
      else if e = cmp_eAC t then -1 else if e = cmp_eBC t then -1 else comparison_sign x0 e := by
    intro e; rw [hS _ (cmp_swap_block _ _ _ hb02) e]
    simp [ha, hb, hd, Equiv.swap_apply_of_ne_of_ne, hn01, hn02, hn12, hn01.symm, hn02.symm,
      hn12.symm, l01, l02, l12, not_lt.mpr l01.le, not_lt.mpr l02.le, not_lt.mpr l12.le]
  have T2 : ∀ e, comparison_sign (x0.trans (Equiv.swap r0 r1)) e = if e = cmp_eAB t then -1
      else if e = cmp_eAC t then 1 else if e = cmp_eBC t then 1 else comparison_sign x0 e := by
    intro e; rw [hS _ (cmp_swap_block _ _ _ hb01) e]
    simp [ha, hb, hd, Equiv.swap_apply_of_ne_of_ne, hn01, hn02, hn12, hn01.symm, hn02.symm,
      hn12.symm, l01, l02, l12, not_lt.mpr l01.le, not_lt.mpr l02.le, not_lt.mpr l12.le]
  have T3 : ∀ e, comparison_sign (x0.trans (Equiv.swap r0 r2 * Equiv.swap r0 r1)) e =
      if e = cmp_eAB t then 1
      else if e = cmp_eAC t then -1 else if e = cmp_eBC t then -1 else comparison_sign x0 e := by
    intro e
    rw [hS _ (fun k => by rw [Equiv.Perm.mul_apply, cmp_swap_block _ _ _ hb02,
      cmp_swap_block _ _ _ hb01]) e]
    simp [ha, hb, hd, Equiv.swap_apply_of_ne_of_ne, hn01, hn02, hn12, hn01.symm, hn02.symm,
      hn12.symm, l01, l02, l12, not_lt.mpr l01.le, not_lt.mpr l02.le, not_lt.mpr l12.le]
  have T4 : ∀ e, comparison_sign (x0.trans (Equiv.swap r1 r2)) e = if e = cmp_eAB t then 1
      else if e = cmp_eAC t then 1 else if e = cmp_eBC t then -1 else comparison_sign x0 e := by
    intro e; rw [hS _ (cmp_swap_block _ _ _ hb12) e]
    simp [ha, hb, hd, Equiv.swap_apply_of_ne_of_ne, hn01, hn02, hn12, hn01.symm, hn02.symm,
      hn12.symm, l01, l02, l12, not_lt.mpr l01.le, not_lt.mpr l02.le, not_lt.mpr l12.le]
  have T5 : ∀ e, comparison_sign (x0.trans (Equiv.swap r0 r1 * Equiv.swap r0 r2)) e =
      if e = cmp_eAB t then -1
      else if e = cmp_eAC t then -1 else if e = cmp_eBC t then 1 else comparison_sign x0 e := by
    intro e
    rw [hS _ (fun k => by rw [Equiv.Perm.mul_apply, cmp_swap_block _ _ _ hb01,
      cmp_swap_block _ _ _ hb02]) e]
    simp [ha, hb, hd, Equiv.swap_apply_of_ne_of_ne, hn01, hn02, hn12, hn01.symm, hn02.symm,
      hn12.symm, l01, l02, l12, not_lt.mpr l01.le, not_lt.mpr l02.le, not_lt.mpr l12.le]
  have hlin : ∀ e : comparison_edge n, (Sum.inl (some e) : comparison_feature2 n) ≠ cmp_qA t ∧
      (Sum.inl (some e) : comparison_feature2 n) ≠ cmp_qB t ∧
      (Sum.inl (some e) : comparison_feature2 n) ≠ cmp_qC t := by
    intro e; simp [cmp_qA, cmp_qB, cmp_qC]
  constructor
  · have H := cmp_comb4 hc (x0.trans 1) (x0.trans (Equiv.swap r0 r2))
      (x0.trans (Equiv.swap r0 r1)) (x0.trans (Equiv.swap r0 r2 * Equiv.swap r0 r1))
      (fun i => (if i = cmp_qA t then 4 else 0) + (if i = cmp_qB t then 4 else 0)) (by
        intro i
        rcases i with (_ | e) | ⟨S, hS⟩
        · simp [comparison_phi2, comparison_phi1, cmp_O_ne_qA, cmp_O_ne_qB]
        · simp only [comparison_phi2, comparison_phi1, T0, T1, T2, T3, (hlin e).1, (hlin e).2.1,
            if_false]
          split_ifs <;> ring
        · obtain ⟨e, f, hef, rfl⟩ := Finset.card_eq_two.mp hS
          simp only [comparison_phi2, Finset.prod_pair hef, T0, T1, T2, T3, cmp_qA, cmp_qB,
            Sum.inr.injEq, Subtype.mk.injEq, cmp_finset_pair_eq_pair]
          rcases cmp_edge_cases t e with rfl | rfl | rfl | ⟨g1, g2, g3⟩ <;>
            rcases cmp_edge_cases t f with rfl | rfl | rfl | ⟨k1, k2, k3⟩
          all_goals first
            | exact absurd rfl hef
            | (simp [cmp_eAB_ne_eAC, cmp_eAB_ne_eBC, cmp_eAC_ne_eBC, cmp_eAC_ne_eAB,
                cmp_eBC_ne_eAB, cmp_eBC_ne_eAC, *] <;> ring_nf))
    simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at H
    linarith
  · have H := cmp_comb4 hc (x0.trans 1) (x0.trans (Equiv.swap r0 r2))
      (x0.trans (Equiv.swap r1 r2)) (x0.trans (Equiv.swap r0 r1 * Equiv.swap r0 r2))
      (fun i => (if i = cmp_qB t then 4 else 0) + (if i = cmp_qC t then 4 else 0)) (by
        intro i
        rcases i with (_ | e) | ⟨S, hS⟩
        · simp [comparison_phi2, comparison_phi1, cmp_O_ne_qB, cmp_O_ne_qC]
        · simp only [comparison_phi2, comparison_phi1, T0, T1, T4, T5, (hlin e).2.1,
            (hlin e).2.2, if_false]
          split_ifs <;> ring
        · obtain ⟨e, f, hef, rfl⟩ := Finset.card_eq_two.mp hS
          simp only [comparison_phi2, Finset.prod_pair hef, T0, T1, T4, T5, cmp_qB, cmp_qC,
            Sum.inr.injEq, Subtype.mk.injEq, cmp_finset_pair_eq_pair]
          rcases cmp_edge_cases t e with rfl | rfl | rfl | ⟨g1, g2, g3⟩ <;>
            rcases cmp_edge_cases t f with rfl | rfl | rfl | ⟨k1, k2, k3⟩
          all_goals first
            | exact absurd rfl hef
            | (simp [cmp_eAB_ne_eAC, cmp_eAB_ne_eBC, cmp_eAC_ne_eBC, cmp_eAC_ne_eAB,
                cmp_eBC_ne_eAB, cmp_eBC_ne_eAC, *] <;> ring_nf))
    simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at H
    linarith

end

section
variable {n : ℕ}

def cmp_beta4 (k : Fin n) : ℕ := if k.val < 2 then 0 else if k.val < 4 then 2 else k.val

theorem cmp_beta4_mono : Monotone (cmp_beta4 (n := n)) := by
  intro i j h
  simp only [cmp_beta4]
  rw [Fin.le_def] at h
  split_ifs <;> omega

theorem cmp_dis_sign_cases (e f : comparison_edge n) (x0 : Equiv.Perm (Fin n))
    (h0 : (x0 e.1.1).val = 0) (h1 : (x0 e.1.2).val = 1) (h2 : (x0 f.1.1).val = 2)
    (h3 : (x0 f.1.2).val = 3)
    (ρ : Equiv.Perm (Fin n)) (hρ : ∀ k, cmp_beta4 (ρ k) = cmp_beta4 k) (g : comparison_edge n) :
    comparison_sign (x0.trans ρ) g =
      if g = e then (if ρ (x0 e.1.1) < ρ (x0 e.1.2) then 1 else -1)
      else if g = f then (if ρ (x0 f.1.1) < ρ (x0 f.1.2) then 1 else -1)
      else comparison_sign x0 g := by
  by_cases g1 : g = e
  · rw [if_pos g1, g1]; rfl
  rw [if_neg g1]
  by_cases g2 : g = f
  · rw [if_pos g2, g2]; rfl
  rw [if_neg g2]
  apply cmp_sign_block cmp_beta4 cmp_beta4_mono ρ hρ
  intro hb
  have hne : (x0 g.1.1).val ≠ (x0 g.1.2).val := fun h' =>
    (ne_of_lt g.2) (x0.injective (Fin.ext h'))
  have hlt : (x0 g.1.1).val < (x0 g.1.2).val ∨ (x0 g.1.2).val < (x0 g.1.1).val := by omega
  simp only [cmp_beta4] at hb
  have hcase : ((x0 g.1.1).val < 2 ∧ (x0 g.1.2).val < 2) ∨
      ((2 ≤ (x0 g.1.1).val ∧ (x0 g.1.1).val < 4) ∧ (2 ≤ (x0 g.1.2).val ∧ (x0 g.1.2).val < 4)) := by
    split_ifs at hb <;> omega
  have hg := g.2
  have he := e.2
  have hf := f.2
  obtain ⟨⟨g1', g2'⟩, hg'⟩ := g
  obtain ⟨⟨e1, e2⟩, he'⟩ := e
  obtain ⟨⟨f1, f2⟩, hf'⟩ := f
  simp only at h0 h1 h2 h3 hcase hg he hf hne g1 g2
  simp only [Fin.lt_def] at hg he hf
  have hl : ∀ v : Fin n, ∀ k : ℕ, (x0 v).val = k → ∀ w : Fin n, (x0 w).val = k → v = w :=
    fun v k hv w hw => x0.injective (Fin.ext (hv.trans hw.symm))
  rcases hcase with ⟨c1, c2⟩ | ⟨⟨c1, c1'⟩, c2, c2'⟩
  · have A : g1' = e1 ∨ g1' = e2 := by
      rcases (show (x0 g1').val = 0 ∨ (x0 g1').val = 1 by omega) with h | h
      · exact Or.inl (hl _ _ h _ h0)
      · exact Or.inr (hl _ _ h _ h1)
    have B : g2' = e1 ∨ g2' = e2 := by
      rcases (show (x0 g2').val = 0 ∨ (x0 g2').val = 1 by omega) with h | h
      · exact Or.inl (hl _ _ h _ h0)
      · exact Or.inr (hl _ _ h _ h1)
    apply g1
    rcases A with rfl | rfl <;> rcases B with rfl | rfl <;> first | rfl | (exfalso; omega)
  · have A : g1' = f1 ∨ g1' = f2 := by
      rcases (show (x0 g1').val = 2 ∨ (x0 g1').val = 3 by omega) with h | h
      · exact Or.inl (hl _ _ h _ h2)
      · exact Or.inr (hl _ _ h _ h3)
    have B : g2' = f1 ∨ g2' = f2 := by
      rcases (show (x0 g2').val = 2 ∨ (x0 g2').val = 3 by omega) with h | h
      · exact Or.inl (hl _ _ h _ h2)
      · exact Or.inr (hl _ _ h _ h3)
    apply g2
    rcases A with rfl | rfl <;> rcases B with rfl | rfl <;> first | rfl | (exfalso; omega)

theorem cmp_dis_rel {c : comparison_feature2 n → ℝ}
    (hc : ∀ x : Equiv.Perm (Fin n), ∑ i, comparison_phi2 x i * c i = 0)
    (e f : comparison_edge n) (hef : e ≠ f)
    (d1 : e.1.1 ≠ f.1.1) (d2 : e.1.1 ≠ f.1.2) (d3 : e.1.2 ≠ f.1.1) (d4 : e.1.2 ≠ f.1.2) :
    c (Sum.inr ⟨{e, f}, Finset.card_pair hef⟩) = 0 := by
  classical
  have he : e.1.1 < e.1.2 := e.2
  have hf : f.1.1 < f.1.2 := f.2
  have h4 : 4 ≤ n := by
    have hcard : ({e.1.1, e.1.2, f.1.1, f.1.2} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [ne_of_lt he, d1, d2]),
        Finset.card_insert_of_notMem (by simp [d3, d4]),
        Finset.card_pair (ne_of_lt hf)]
    have := Finset.card_le_univ ({e.1.1, e.1.2, f.1.1, f.1.2} : Finset (Fin n))
    rw [hcard, Fintype.card_fin] at this
    exact this
  obtain ⟨x0, h0, h1, h2, h3⟩ := cmp_exists_perm4 e.1.1 e.1.2 f.1.1 f.1.2 (ne_of_lt he) d1 d2
    d3 d4 (ne_of_lt hf) h4
  set r0 : Fin n := ⟨0, by omega⟩ with hr0
  set r1 : Fin n := ⟨1, by omega⟩ with hr1
  set r2 : Fin n := ⟨2, by omega⟩ with hr2
  set r3 : Fin n := ⟨3, by omega⟩ with hr3
  have ha : x0 e.1.1 = r0 := Fin.ext h0
  have hb : x0 e.1.2 = r1 := Fin.ext h1
  have hd : x0 f.1.1 = r2 := Fin.ext h2
  have hg : x0 f.1.2 = r3 := Fin.ext h3
  have hb01 : cmp_beta4 r0 = cmp_beta4 r1 := by simp [cmp_beta4, r0, r1]
  have hb23 : cmp_beta4 r2 = cmp_beta4 r3 := by simp [cmp_beta4, r2, r3]
  have hn01 : r0 ≠ r1 := by simp [r0, r1]
  have hn23 : r2 ≠ r3 := by simp [r2, r3]
  have hn02 : r0 ≠ r2 := by simp [r0, r2]
  have hn03 : r0 ≠ r3 := by simp [r0, r3]
  have hn12 : r1 ≠ r2 := by simp [r1, r2]
  have hn13 : r1 ≠ r3 := by simp [r1, r3]
  have l01 : r0 < r1 := by simp [r0, r1, Fin.lt_def]
  have l23 : r2 < r3 := by simp [r2, r3, Fin.lt_def]
  have hS := cmp_dis_sign_cases e f x0 h0 h1 h2 h3
  have T0 : ∀ g, comparison_sign (x0.trans 1) g =
      if g = e then 1 else if g = f then 1 else comparison_sign x0 g := by
    intro g; rw [hS 1 (fun k => rfl) g]; simp [ha, hb, hd, hg, l01, l23]
  have T1 : ∀ g, comparison_sign (x0.trans (Equiv.swap r0 r1 * Equiv.swap r2 r3)) g =
      if g = e then -1 else if g = f then -1 else comparison_sign x0 g := by
    intro g
    rw [hS _ (fun k => by rw [Equiv.Perm.mul_apply, cmp_swap_block _ _ _ hb01,
      cmp_swap_block _ _ _ hb23]) g]
    simp [ha, hb, hd, hg, Equiv.swap_apply_of_ne_of_ne, hn01, hn23, hn02, hn03, hn12, hn13,
      hn01.symm, hn23.symm, hn02.symm, hn03.symm, hn12.symm, hn13.symm, l01, l23,
      not_lt.mpr l01.le, not_lt.mpr l23.le]
  have T2 : ∀ g, comparison_sign (x0.trans (Equiv.swap r0 r1)) g =
      if g = e then -1 else if g = f then 1 else comparison_sign x0 g := by
    intro g
    rw [hS _ (cmp_swap_block _ _ _ hb01) g]
    simp [ha, hb, hd, hg, Equiv.swap_apply_of_ne_of_ne, hn01, hn23, hn02, hn03, hn12, hn13,
      hn01.symm, hn23.symm, hn02.symm, hn03.symm, hn12.symm, hn13.symm, l01, l23,
      not_lt.mpr l01.le, not_lt.mpr l23.le]
  have T3 : ∀ g, comparison_sign (x0.trans (Equiv.swap r2 r3)) g =
      if g = e then 1 else if g = f then -1 else comparison_sign x0 g := by
    intro g
    rw [hS _ (cmp_swap_block _ _ _ hb23) g]
    simp [ha, hb, hd, hg, Equiv.swap_apply_of_ne_of_ne, hn01, hn23, hn02, hn03, hn12, hn13,
      hn01.symm, hn23.symm, hn02.symm, hn03.symm, hn12.symm, hn13.symm, l01, l23,
      not_lt.mpr l01.le, not_lt.mpr l23.le]
  have H := cmp_comb4 hc (x0.trans 1) (x0.trans (Equiv.swap r0 r1 * Equiv.swap r2 r3))
      (x0.trans (Equiv.swap r0 r1)) (x0.trans (Equiv.swap r2 r3))
      (fun i => if i = Sum.inr ⟨{e, f}, Finset.card_pair hef⟩ then 4 else 0) (by
        intro i
        rcases i with (_ | g) | ⟨S, hS⟩
        · simp [comparison_phi2, comparison_phi1]
        · simp only [comparison_phi2, comparison_phi1, T0, T1, T2, T3, reduceCtorEq, if_false]
          split_ifs <;> ring
        · obtain ⟨g, k, hgk, rfl⟩ := Finset.card_eq_two.mp hS
          simp only [comparison_phi2, Finset.prod_pair hgk, T0, T1, T2, T3,
            Sum.inr.injEq, Subtype.mk.injEq, cmp_finset_pair_eq_pair]
          have cl : ∀ q : comparison_edge n, q = e ∨ q = f ∨ (q ≠ e ∧ q ≠ f) := by
            intro q; by_cases h1 : q = e
            · exact Or.inl h1
            by_cases h2 : q = f
            · exact Or.inr (Or.inl h2)
            exact Or.inr (Or.inr ⟨h1, h2⟩)
          rcases cl g with rfl | rfl | ⟨g1, g2⟩ <;> rcases cl k with rfl | rfl | ⟨k1, k2⟩
          all_goals first
            | exact absurd rfl hgk
            | (simp [hef, hef.symm, *] <;> ring_nf))
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at H
  linarith

end

section
variable {n : ℕ}

theorem cmp_pair_classify (e f : comparison_edge n) (hef : e ≠ f) :
    (e.1.1 ≠ f.1.1 ∧ e.1.1 ≠ f.1.2 ∧ e.1.2 ≠ f.1.1 ∧ e.1.2 ≠ f.1.2) ∨
    ∃ t : comparison_triangle n, ({e, f} : Finset (comparison_edge n)) = {cmp_eAB t, cmp_eAC t} ∨
      ({e, f} : Finset (comparison_edge n)) = {cmp_eAB t, cmp_eBC t} ∨
      ({e, f} : Finset (comparison_edge n)) = {cmp_eAC t, cmp_eBC t} := by
  obtain ⟨⟨e1, e2⟩, he⟩ := e
  obtain ⟨⟨f1, f2⟩, hf⟩ := f
  have hef' : ¬ (e1 = f1 ∧ e2 = f2) := fun h => hef (by obtain ⟨rfl, rfl⟩ := h; rfl)
  by_cases d1 : e1 = f1
  · subst d1
    have d4 : e2 ≠ f2 := fun h => hef' ⟨rfl, h⟩
    rcases lt_or_gt_of_ne d4 with h | h
    · exact Or.inr ⟨⟨(e1, e2, f2), he, h⟩, Or.inl rfl⟩
    · exact Or.inr ⟨⟨(e1, f2, e2), hf, h⟩, Or.inl (Finset.pair_comm _ _)⟩
  by_cases d2 : e1 = f2
  · subst d2
    exact Or.inr ⟨⟨(f1, e1, e2), hf, he⟩, Or.inr (Or.inl (Finset.pair_comm _ _))⟩
  by_cases d3 : e2 = f1
  · subst d3
    exact Or.inr ⟨⟨(e1, e2, f2), he, hf⟩, Or.inr (Or.inl rfl)⟩
  by_cases d4 : e2 = f2
  · subst d4
    rcases lt_or_gt_of_ne d1 with h | h
    · exact Or.inr ⟨⟨(e1, f1, e2), h, hf⟩, Or.inr (Or.inr rfl)⟩
    · exact Or.inr ⟨⟨(f1, e1, e2), h, he⟩, Or.inr (Or.inr (Finset.pair_comm _ _))⟩
  exact Or.inl ⟨d1, d2, d3, d4⟩

end

theorem comparison_eval_ker_le_span_kappa (n : ℕ) :
    LinearMap.ker (comparison_eval_matrix n).mulVecLin ≤
      Submodule.span ℝ (Set.range (comparison_triangle_kappa (n := n))) := by
  classical
  intro c hc
  have hc0 := cmp_ker_eval hc
  set p : comparison_triangle n → ℝ := fun t => c (cmp_qA t) with hp
  set c' : comparison_feature2 n → ℝ := c - ∑ t, p t • comparison_triangle_kappa t with hc'def
  have hkap : ∀ (x : Equiv.Perm (Fin n)) (t : comparison_triangle n),
      ∑ i, comparison_phi2 x i * comparison_triangle_kappa t i = 0 := by
    intro x t
    have := congrFun (comparison_triangle_kappa_mem_eval_ker n t) x
    simpa [Matrix.mulVec, dotProduct, comparison_eval_matrix] using this
  have hk : ∀ x : Equiv.Perm (Fin n), ∑ i, comparison_phi2 x i * c' i = 0 := by
    intro x
    have e1 : ∀ i, comparison_phi2 x i * c' i = comparison_phi2 x i * c i -
        ∑ t, p t * (comparison_phi2 x i * comparison_triangle_kappa t i) := by
      intro i
      simp only [c', Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
        Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun t _ => by ring)
    simp only [e1, Finset.sum_sub_distrib, hc0 x]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, hkap x]
  have hA : ∀ t, c' (cmp_qA t) = 0 := by
    intro t
    simp only [c', Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cmp_kappa_qA,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hp, sub_self]
  have hrel := cmp_tri_rel hk
  have hB : ∀ t, c' (cmp_qB t) = 0 := fun t => by
    have := (hrel t).1; rw [hA t] at this; linarith
  have hC : ∀ t, c' (cmp_qC t) = 0 := fun t => by
    have := (hrel t).2; rw [hB t] at this; linarith
  have hq : ∀ s : {s : Finset (comparison_edge n) // s.card = 2}, c' (Sum.inr s) = 0 := by
    rintro ⟨S, hS⟩
    obtain ⟨e, f, hef, rfl⟩ := Finset.card_eq_two.mp hS
    rcases cmp_pair_classify e f hef with ⟨d1, d2, d3, d4⟩ | ⟨t, h | h | h⟩
    · exact cmp_dis_rel hk e f hef d1 d2 d3 d4
    · have : (Sum.inr ⟨{e, f}, hS⟩ : comparison_feature2 n) = cmp_qA t := by
        simp only [cmp_qA, Sum.inr.injEq, Subtype.mk.injEq]; exact h
      rw [this]; exact hA t
    · have : (Sum.inr ⟨{e, f}, hS⟩ : comparison_feature2 n) = cmp_qB t := by
        simp only [cmp_qB, Sum.inr.injEq, Subtype.mk.injEq]; exact h
      rw [this]; exact hB t
    · have : (Sum.inr ⟨{e, f}, hS⟩ : comparison_feature2 n) = cmp_qC t := by
        simp only [cmp_qC, Sum.inr.injEq, Subtype.mk.injEq]; exact h
      rw [this]; exact hC t
  have hl : ∀ e, c' (Sum.inl (some e)) = 0 := cmp_lin_zero hk
  have h0 : c' (Sum.inl none) = 0 := by
    have := hk 1
    simpa [Fintype.sum_sum_type, Fintype.sum_option, hl, hq, comparison_phi2,
      comparison_phi1] using this
  have hzero : c' = 0 := by
    funext i
    rcases i with (_ | e) | s
    exacts [h0, hl e, hq s]
  have hceq : c = ∑ t, p t • comparison_triangle_kappa t := sub_eq_zero.mp hzero
  rw [hceq]
  exact Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩))
