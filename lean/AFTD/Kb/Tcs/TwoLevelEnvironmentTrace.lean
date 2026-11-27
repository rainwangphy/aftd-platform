import AFTD.Prelude
import AFTD.Kb.Tcs.TwoLevelEnvironment

/-!
# two_level_environment_trace

Topic: quantum   Node: 8575fb4a5d8e

Provenance: helper lemma. Sanity lemma for two_level_environment, serving OP-2466: it has trace one.

For d ≥ 2 and 0 ≤ p ≤ 1 and every real t, the trace of two_level_environment d p t is 1.
-/

theorem two_level_environment_trace (d : ℕ) (hd : 2 ≤ d) (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (two_level_environment d p t).trace = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hd
    exact ⟨n, by omega⟩
  change ∑ j : Fin (n + 2), two_level_environment (n + 2) p t j j = 1
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have h1 : (Fin.succ (0 : Fin (n + 1)) : Fin (n + 2)) = 1 := rfl
  rw [h1]
  dsimp [two_level_environment]
  simp only [mul_zero, add_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hp : (√p : ℂ) * (√p : ℂ) = (p : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt hp0
  have hp' : (√(1 - p) : ℂ) * (√(1 - p) : ℂ) = (1 - p : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (by linarith)
  rw [mul_assoc (t : ℂ), hp, mul_assoc (t : ℂ), hp']
  push_cast
  have hn : ((n : ℂ) + 2) ≠ 0 := by norm_cast
  field_simp
  ring
