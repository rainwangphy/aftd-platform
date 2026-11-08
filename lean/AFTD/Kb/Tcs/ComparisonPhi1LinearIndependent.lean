import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonPhi1
import AFTD.Kb.Tcs.ComparisonFeature1
import AFTD.Kb.Tcs.ComparisonEdge
import AFTD.Kb.Tcs.ComparisonSign
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# comparison_phi1_linearIndependent

Topic: quantum   Node: c3eb76fb058d

Provenance: helper lemma. Step of arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, Lemma 1 (quadratic_comparison_evaluation_kernel_and_projector)

The constant function 1 and the comparison signs d_e, e an edge of [n], are linearly independent real functions on strict orders (permutations of Fin n).
-/

theorem comparison_phi1_linearIndependent (n : ℕ) :
    LinearIndependent ℝ
      (fun i : comparison_feature1 n => fun x : Equiv.Perm (Fin n) => comparison_phi1 x i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hx : ∀ x : Equiv.Perm (Fin n),
      g none + ∑ e : comparison_edge n, g (some e) * comparison_sign x e = 0 := by
    intro x
    have := congrFun hg x
    simpa [Fintype.sum_option, comparison_phi1] using this
  have hedge : ∀ e : comparison_edge n, g (some e) = 0 := by
    intro e0
    obtain ⟨⟨a, b⟩, hab⟩ := e0
    have hab' : a < b := hab
    have hb := b.isLt
    have hav : a.val < b.val := hab'
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    let σ : Equiv.Perm (Fin n) := Equiv.swap a i0
    let x : Equiv.Perm (Fin n) := σ.trans (Equiv.swap (σ b) i1)
    let y : Equiv.Perm (Fin n) := x.trans (Equiv.swap i0 i1)
    have hσb : σ b ≠ i0 := by
      intro h
      have : σ b = σ a := by simp [σ, h]
      exact (ne_of_lt hab') (σ.injective this).symm
    have hxa : x a = i0 := by
      have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
      simp only [x, Equiv.trans_apply, σ, Equiv.swap_apply_left]
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hσb) h01]
    have hxb : x b = i1 := by
      simp only [x, Equiv.trans_apply, Equiv.swap_apply_left]
    have hy : ∀ j, y j = Equiv.swap i0 i1 (x j) := fun j => rfl
    have key : ∀ f : comparison_edge n, f ≠ ⟨(a, b), hab⟩ →
        comparison_sign y f = comparison_sign x f := by
      intro f hf
      obtain ⟨⟨p, q⟩, hpq⟩ := f
      have hpq' : p < q := hpq
      have hne : ¬ (x p = i0 ∧ x q = i1) := by
        rintro ⟨h1, h2⟩
        apply hf
        have : p = a := x.injective (h1.trans hxa.symm)
        have : q = b := x.injective (h2.trans hxb.symm)
        subst_vars; rfl
      have hne2 : ¬ (x p = i1 ∧ x q = i0) := by
        rintro ⟨h1, h2⟩
        have : p = b := x.injective (h1.trans hxb.symm)
        have : q = a := x.injective (h2.trans hxa.symm)
        subst_vars
        exact absurd (hpq'.trans hab') (lt_irrefl _)
      have hpq_ne : x p ≠ x q := fun h => (ne_of_lt hpq') (x.injective h)
      simp only [comparison_sign, hy]
      rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
      simp only [Fin.ext_iff, Fin.lt_def, i0, i1] at hne hne2 hpq_ne ⊢
      split_ifs <;> simp_all <;> omega
    have hsx : comparison_sign x ⟨(a, b), hab⟩ = 1 := by
      simp [comparison_sign, hxa, hxb, i0, i1, Fin.lt_def]
    have hsy : comparison_sign y ⟨(a, b), hab⟩ = -1 := by
      simp [comparison_sign, hy, hxa, hxb, i0, i1, Fin.lt_def]
    have h1 := hx x
    have h2 := hx y
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨(a, b), hab⟩)] at h1 h2
    have hrest : ∑ e ∈ Finset.univ.erase ⟨(a, b), hab⟩, g (some e) * comparison_sign y e =
        ∑ e ∈ Finset.univ.erase ⟨(a, b), hab⟩, g (some e) * comparison_sign x e := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [key f (Finset.ne_of_mem_erase hf)]
    rw [hrest, hsy] at h2
    rw [hsx] at h1
    linarith
  have h0 := hx 1
  simp only [hedge, zero_mul, Finset.sum_const_zero, add_zero] at h0
  intro i
  cases i with
  | none => exact h0
  | some e => exact hedge e
