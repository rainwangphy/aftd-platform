import AFTD.Prelude
import AFTD.Kb.Tcs.PhaseQueryComputesCleanly

/-!
# zero_clean_phase_queries_only_constant

Topic: quantum   Node: 5f88d3aa3457

Provenance: helper lemma. Elementary base case for clean phase query circuits.

A clean phase circuit using no queries computes a constant Boolean function.
-/

open scoped BigOperators

/-- Zero clean phase queries imply a constant function. -/
theorem zero_clean_phase_queries_only_constant {N : ℕ} (f : (Fin N → Bool) → Bool)
    (h : phase_query_computes_cleanly f 0) : ∀ x y, f x = f y := by
  obtain ⟨B, instF, instD, reg, ψ, hψ, U0, hU0, steps, hsteps, hresult⟩ := h
  letI := instF
  letI := instD
  intro x y
  by_contra hxy
  have hs : (if f x then (-1 : ℂ) else 1) ≠ (if f y then (-1 : ℂ) else 1) := by
    cases hfx : f x <;> cases hfy : f y
    · exact (hxy (hfx.trans hfy.symm)).elim
    · norm_num [hfx, hfy]
    · norm_num [hfx, hfy]
    · exact (hxy (hfx.trans hfy.symm)).elim
  have hz : ∀ b, ψ b = 0 := by
    intro b
    have hx := hresult x b
    have hy := hresult y b
    simp only [List.ofFn_zero, List.foldl_nil] at hx hy
    have hh : ((if f x then (-1 : ℂ) else 1) - (if f y then (-1 : ℂ) else 1)) * ψ b = 0 := by
      linear_combination hy - hx
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hs)
  have hsum : (∑ b, Complex.normSq (ψ b)) = 0 := by simp [hz]
  linarith
