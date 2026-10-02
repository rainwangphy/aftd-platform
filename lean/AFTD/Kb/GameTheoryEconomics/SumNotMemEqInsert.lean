import AFTD.Prelude

/-!
# sum_not_mem_eq_insert

Topic: general_equilibrium   Node: 7274bb79eff0

For any function G on coalitions, the sum of G(S with i) over coalitions S avoiding i equals the sum of G(T) over coalitions T containing i.
-/

/-- Adding `i` is a bijection from the sets avoiding `i` onto the sets containing `i`. -/
theorem sum_not_mem_eq_insert {n : ℕ} (G : Finset (Fin n) → ℝ) (i : Fin n) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∉ S), G (insert i S)
      = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => i ∈ T), G T := by
  apply Finset.sum_nbij' (fun S => insert i S) (fun T => T.erase i)
  · intro S hS; simp
  · intro T hT; simp
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.erase_insert hS
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    exact Finset.insert_erase hT
  · intro S _; rfl
