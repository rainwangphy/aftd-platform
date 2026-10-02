import AFTD.Prelude

/-!
# sum_not_mem_card_eq_insert

Topic: general_equilibrium   Node: c475c135602a

For any function G on coalitions, the sum of G(S with i) over k-element coalitions S avoiding i equals the sum of G(T) over (k+1)-element coalitions T containing i.
-/

/-- Adding `i` is a bijection from the `k`-sets avoiding `i` onto the `(k+1)`-sets containing `i`. -/
theorem sum_not_mem_card_eq_insert {n : ℕ} (G : Finset (Fin n) → ℝ) (i : Fin n) (k : ℕ) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∉ S ∧ S.card = k), G (insert i S)
      = ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => i ∈ T ∧ T.card = k + 1), G T := by
  apply Finset.sum_nbij' (fun S => insert i S) (fun T => T.erase i)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact ⟨Finset.mem_insert_self i S, by rw [Finset.card_insert_of_notMem hS.1, hS.2]⟩
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    exact ⟨Finset.notMem_erase i T, by rw [Finset.card_erase_of_mem hT.1, hT.2]; rfl⟩
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.erase_insert hS.1
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    exact Finset.insert_erase hT.1
  · intro S _; rfl
