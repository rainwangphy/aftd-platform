import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SwingTable

/-!
# swing_table_cast_eq_sum

Topic: general_equilibrium   Node: 87d80a5b9e4b

For a monotone game, T(i, k) equals the sum over coalitions S of size k not containing i of v(S with i) - v(S).
-/

/-- For a monotone game, the swing count `T i k` is the sum, over coalitions `S` of size `k` not containing `i`, of `v(S ∪ {i}) - v(S)`. -/
theorem swing_table_cast_eq_sum {n : ℕ} (v : Finset (Fin n) → Bool)
    (hv : ∀ S T, S ⊆ T → v S = true → v T = true) (i : Fin n) (k : ℕ) :
    (swing_table v i k : ℝ) = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∉ S ∧ S.card = k),
      ((if v (insert i S) then 1 else 0) - (if v S then 1 else 0)) := by
  have e : (Finset.univ.filter fun S : Finset (Fin n) =>
      i ∉ S ∧ S.card = k ∧ v (insert i S) = true ∧ v S = false)
      = (Finset.univ.filter fun S : Finset (Fin n) => i ∉ S ∧ S.card = k).filter
          (fun S => v (insert i S) = true ∧ v S = false) := by
    ext S; simp [and_assoc]
  unfold swing_table
  rw [e, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro S _
  have := hv S (insert i S) (Finset.subset_insert i S)
  cases h1 : v (insert i S) <;> cases h2 : v S <;> simp_all
