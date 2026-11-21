import AFTD.Prelude
import AFTD.Kb.Optimization.SsssPrimalFeasible
import AFTD.Kb.Optimization.SsssDualFeasible
import AFTD.Kb.Optimization.SsssPrimalObj
import AFTD.Kb.Optimization.SsssDualObj
import AFTD.Kb.Optimization.SsssCuts

/-!
# ssss_weak_duality

Topic: lp_duality   Node: c61d74d00ae1

Provenance: helper lemma. arXiv:2611.26188, Section 3

For any edge set E : Finset (V × V), edge costs c : V × V → ℝ, distinct terminals s ≠ t in V, and integer k : ℕ, if x : V × V → ℝ is feasible for the primal LP (SSSS-P) with k paths and (a, y) is feasible for the dual LP (SSSS-D), then the dual objective value ssss_dual_obj s t k a y is at most the primal objective value ssss_primal_obj E c x.
-/

theorem ssss_weak_duality_sum_flow_potentials {V : Type*} [Fintype V] [DecidableEq V]
    (s t : V) (hst : s ≠ t) (k : ℕ) (a : V → ℝ) :
    ∑ v : V, a v * (if v = s then -↑k else if v = t then ↑k else 0) =
    ↑k * (a t - a s) := by
  have h1 : ∀ v : V, a v * (if v = s then -↑k else if v = t then ↑k else 0) =
      (if v = s then -(↑k * a s) else 0) + (if v = t then ↑k * a t else 0) := by
    intro v
    by_cases hvs : v = s
    · subst hvs
      rw [if_pos rfl, if_pos rfl, if_neg hst]
      ring
    · rw [if_neg hvs, if_neg hvs]
      by_cases hvt : v = t
      · subst hvt
        rw [if_pos rfl, if_pos rfl]
        ring
      · rw [if_neg hvt, if_neg hvt]
        ring
  simp_rw [h1, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ s, Finset.sum_ite_eq' Finset.univ t]
  · simp only [Finset.mem_univ, if_true]
    ring

theorem ssss_weak_duality_sum_potentials_flow {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (x : V × V → ℝ) (a : V → ℝ) :
    ∑ v : V, a v * (∑ e ∈ E with e.2 = v, x e - ∑ e ∈ E with e.1 = v, x e) =
    ∑ e ∈ E, (a e.2 - a e.1) * x e := by
  have h_in : (∑ v : V, a v * ∑ e ∈ E with e.2 = v, x e) = ∑ e ∈ E, a e.2 * x e := by
    simp_rw [Finset.mul_sum]
    have h1 : ∀ v : V, (∑ e ∈ E with e.2 = v, a v * x e) = ∑ e ∈ E with e.2 = v, a e.2 * x e := by
      intro v
      apply Finset.sum_congr rfl
      intro e he
      have he2 : e.2 = v := (Finset.mem_filter.mp he).2
      rw [he2]
    simp_rw [h1]
    exact Finset.sum_fiberwise E Prod.snd (fun e => a e.2 * x e)
  have h_out : (∑ v : V, a v * ∑ e ∈ E with e.1 = v, x e) = ∑ e ∈ E, a e.1 * x e := by
    simp_rw [Finset.mul_sum]
    have h1 : ∀ v : V, (∑ e ∈ E with e.1 = v, a v * x e) = ∑ e ∈ E with e.1 = v, a e.1 * x e := by
      intro v
      apply Finset.sum_congr rfl
      intro e he
      have he1 : e.1 = v := (Finset.mem_filter.mp he).2
      rw [he1]
    simp_rw [h1]
    exact Finset.sum_fiberwise E Prod.fst (fun e => a e.1 * x e)
  have h_sub : (∑ v : V, a v * (∑ e ∈ E with e.2 = v, x e - ∑ e ∈ E with e.1 = v, x e)) =
      (∑ v : V, a v * ∑ e ∈ E with e.2 = v, x e) - (∑ v : V, a v * ∑ e ∈ E with e.1 = v, x e) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [h_sub, h_in, h_out]
  simp_rw [sub_mul, Finset.sum_sub_distrib]

theorem ssss_weak_duality_cuts_sum_swap {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (s t : V) (x : V × V → ℝ) (y : Finset V → ℝ) :
    ∑ U ∈ ssss_cuts s t, y U * (∑ e ∈ E with e.1 ∈ U ∧ e.2 ∉ U ∨ e.1 ∉ U ∧ e.2 ∈ U, x e) =
    ∑ e ∈ E, (∑ U ∈ ssss_cuts s t with e.1 ∈ U ∧ e.2 ∉ U ∨ e.1 ∉ U ∧ e.2 ∈ U, y U) * x e := by
  have h1 : (∑ U ∈ ssss_cuts s t, y U * (∑ e ∈ E with e.1 ∈ U ∧ e.2 ∉ U ∨ e.1 ∉ U ∧ e.2 ∈ U, x e)) =
      ∑ U ∈ ssss_cuts s t, ∑ e ∈ E with e.1 ∈ U ∧ e.2 ∉ U ∨ e.1 ∉ U ∧ e.2 ∈ U, y U * x e := by
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.mul_sum]
  have h2 : (∑ e ∈ E, (∑ U ∈ ssss_cuts s t with e.1 ∈ U ∧ e.2 ∉ U ∨ e.1 ∉ U ∧ e.2 ∈ U, y U) * x e) =
      ∑ e ∈ E, ∑ U ∈ ssss_cuts s t with e.1 ∈ U ∧ e.2 ∉ U ∨ e.1 ∉ U ∧ e.2 ∈ U, y U * x e := by
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_mul]
  rw [h1, h2]
  let P := fun (e : V × V) (U : Finset V) => e.1 ∈ U ∧ e.2 ∉ U ∨ e.1 ∉ U ∧ e.2 ∈ U
  have h3 : (∑ U ∈ ssss_cuts s t, ∑ e ∈ E with P e U, y U * x e) =
      ∑ U ∈ ssss_cuts s t, ∑ e ∈ E, if P e U then y U * x e else 0 := by
    apply Finset.sum_congr rfl
    intro U _
    exact Finset.sum_filter (fun e => P e U) (fun e => y U * x e)
  have h4 : (∑ e ∈ E, ∑ U ∈ ssss_cuts s t with P e U, y U * x e) =
      ∑ e ∈ E, ∑ U ∈ ssss_cuts s t, if P e U then y U * x e else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    exact Finset.sum_filter (fun U => P e U) (fun U => y U * x e)
  rw [h3, h4, Finset.sum_comm]

/-- Weak duality for the Single-Source Single-Sink Multi-Path LP relaxation. -/
theorem ssss_weak_duality {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (c : V × V → ℝ) (s t : V) (hst : s ≠ t) (k : ℕ)
    (x : V × V → ℝ) (hx : ssss_primal_feasible E s t k x)
    (a : V → ℝ) (y : Finset V → ℝ) (hy : ssss_dual_feasible E c s t a y) :
    ssss_dual_obj s t k a y ≤ ssss_primal_obj E c x := by
  rcases hx with ⟨hx_nonneg, hx_flow, hx_cut⟩
  rcases hy with ⟨hy_nonneg, hy_cost⟩
  dsimp [ssss_dual_obj, ssss_primal_obj]
  have h_flow_eq : ↑k * (a t - a s) = ∑ e ∈ E, (a e.2 - a e.1) * x e := by
    have h1 : ∑ v : V, a v * (∑ e ∈ E with e.2 = v, x e - ∑ e ∈ E with e.1 = v, x e) =
        ∑ v : V, a v * (if v = s then -↑k else if v = t then ↑k else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hx_flow v]
    rw [ssss_weak_duality_sum_flow_potentials s t hst k a] at h1
    rw [ssss_weak_duality_sum_potentials_flow E x a] at h1
    exact h1.symm
  have h_cut_le : (∑ U ∈ ssss_cuts s t, 2 * y U) ≤
      ∑ e ∈ E, (∑ U ∈ ssss_cuts s t with e.1 ∈ U ∧ e.2 ∉ U ∨ e.1 ∉ U ∧ e.2 ∈ U, y U) * x e := by
    rw [← ssss_weak_duality_cuts_sum_swap]
    apply Finset.sum_le_sum
    intro U hU
    have hU_flow := hx_cut U hU
    have hU_nonneg := hy_nonneg U hU
    nlinarith
  have h_sum_le : (∑ e ∈ E, (a e.2 - a e.1) * x e) +
      ∑ e ∈ E, (∑ U ∈ ssss_cuts s t with e.1 ∈ U ∧ e.2 ∉ U ∨ e.1 ∉ U ∧ e.2 ∈ U, y U) * x e ≤
      ∑ e ∈ E, c e * x e := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e he
    have he_cost := hy_cost e he
    have he_nonneg := hx_nonneg e he
    calc (a e.2 - a e.1) * x e + (∑ U ∈ ssss_cuts s t with e.1 ∈ U ∧ e.2 ∉ U ∨ e.1 ∉ U ∧ e.2 ∈ U, y U) * x e
      _ = ((a e.2 - a e.1) + ∑ U ∈ ssss_cuts s t with e.1 ∈ U ∧ e.2 ∉ U ∨ e.1 ∉ U ∧ e.2 ∈ U, y U) * x e := by ring
      _ ≤ c e * x e := by nlinarith
  linarith
