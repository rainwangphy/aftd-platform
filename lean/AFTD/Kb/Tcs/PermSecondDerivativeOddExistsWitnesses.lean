import AFTD.Prelude
import AFTD.Kb.Tcs.PermSecondDerivative

/-!
# perm_second_derivative_odd_exists_witnesses

Topic: combinatorics   Node: 0b4d38ecbbb9

Provenance: helper lemma. scout/2610-38237-inflection-sets-of-permutations.md:383

For any integer $k \ge 1$, there exist two distinct permutations $\sigma, \pi \in \mathrm{Sym}_{2k+1}$, neither of which is the identity or its reverse, having the same discrete second derivative.
-/

def perm_second_derivative_odd_exists_witnesses_sigma_val (k t : ℕ) : ℕ :=
  if t ≤ k then 2 * t else 2 * t - (2 * k + 1)

def perm_second_derivative_odd_exists_witnesses_pi_val (k t : ℕ) : ℕ :=
  if t ≤ k then t + k else t - (k + 1)

def perm_second_derivative_odd_exists_witnesses_sigma_fn (k : ℕ) (t : Fin (2 * k + 1)) : Fin (2 * k + 1) :=
  ⟨perm_second_derivative_odd_exists_witnesses_sigma_val k t.1, by
    unfold perm_second_derivative_odd_exists_witnesses_sigma_val; split_ifs <;> omega⟩

def perm_second_derivative_odd_exists_witnesses_pi_fn (k : ℕ) (t : Fin (2 * k + 1)) : Fin (2 * k + 1) :=
  ⟨perm_second_derivative_odd_exists_witnesses_pi_val k t.1, by
    unfold perm_second_derivative_odd_exists_witnesses_pi_val; split_ifs <;> omega⟩

theorem perm_second_derivative_odd_exists_witnesses_sigma_fn_inj (k : ℕ) :
    Function.Injective (perm_second_derivative_odd_exists_witnesses_sigma_fn k) := by
  intro a b hab
  apply Fin.ext
  have h := congr_arg Fin.val hab
  dsimp [perm_second_derivative_odd_exists_witnesses_sigma_fn,
         perm_second_derivative_odd_exists_witnesses_sigma_val] at h
  split_ifs at h <;> omega

theorem perm_second_derivative_odd_exists_witnesses_pi_fn_inj (k : ℕ) :
    Function.Injective (perm_second_derivative_odd_exists_witnesses_pi_fn k) := by
  intro a b hab
  apply Fin.ext
  have h := congr_arg Fin.val hab
  dsimp [perm_second_derivative_odd_exists_witnesses_pi_fn,
         perm_second_derivative_odd_exists_witnesses_pi_val] at h
  split_ifs at h <;> omega

noncomputable def perm_second_derivative_odd_exists_witnesses_sigma_perm (k : ℕ) :
    Equiv.Perm (Fin (2 * k + 1)) :=
  Equiv.ofBijective (perm_second_derivative_odd_exists_witnesses_sigma_fn k)
    ((perm_second_derivative_odd_exists_witnesses_sigma_fn_inj k).bijective_of_finite)

noncomputable def perm_second_derivative_odd_exists_witnesses_pi_perm (k : ℕ) :
    Equiv.Perm (Fin (2 * k + 1)) :=
  Equiv.ofBijective (perm_second_derivative_odd_exists_witnesses_pi_fn k)
    ((perm_second_derivative_odd_exists_witnesses_pi_fn_inj k).bijective_of_finite)

/-- Existence of distinct permutations of odd order 2k+1, neither identity nor its reverse, with identical second derivatives. -/
theorem perm_second_derivative_odd_exists_witnesses (k : ℕ) (hk : 1 ≤ k) :
    ∃ (σ π : Equiv.Perm (Fin (2 * k + 1))),
      σ ≠ π ∧
      σ ≠ 1 ∧ σ ≠ Fin.revPerm ∧
      π ≠ 1 ∧ π ≠ Fin.revPerm ∧
      perm_second_derivative σ = perm_second_derivative π := by
  refine ⟨perm_second_derivative_odd_exists_witnesses_sigma_perm k,
          perm_second_derivative_odd_exists_witnesses_pi_perm k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h0 : perm_second_derivative_odd_exists_witnesses_sigma_perm k ⟨0, by omega⟩ =
              perm_second_derivative_odd_exists_witnesses_pi_perm k ⟨0, by omega⟩ := by rw [h]
    have hval := congr_arg Fin.val h0
    dsimp [perm_second_derivative_odd_exists_witnesses_sigma_perm,
           perm_second_derivative_odd_exists_witnesses_pi_perm,
           perm_second_derivative_odd_exists_witnesses_sigma_fn,
           perm_second_derivative_odd_exists_witnesses_pi_fn,
           perm_second_derivative_odd_exists_witnesses_sigma_val,
           perm_second_derivative_odd_exists_witnesses_pi_val] at hval
    omega
  · intro h
    have h1 : perm_second_derivative_odd_exists_witnesses_sigma_perm k ⟨1, by omega⟩ = ⟨1, by omega⟩ := by rw [h]; rfl
    have hval := congr_arg Fin.val h1
    dsimp [perm_second_derivative_odd_exists_witnesses_sigma_perm,
           perm_second_derivative_odd_exists_witnesses_sigma_fn,
           perm_second_derivative_odd_exists_witnesses_sigma_val] at hval
    split_ifs at hval
    omega
  · intro h
    have h0 : perm_second_derivative_odd_exists_witnesses_sigma_perm k ⟨0, by omega⟩ = Fin.revPerm ⟨0, by omega⟩ := by rw [h]
    have hval := congr_arg Fin.val h0
    have hr : ((Fin.revPerm (⟨0, by omega⟩ : Fin (2 * k + 1))) : Fin (2 * k + 1)).val = 2 * k := by
      rw [Fin.revPerm_apply, Fin.val_rev]; rfl
    rw [hr] at hval
    dsimp [perm_second_derivative_odd_exists_witnesses_sigma_perm,
           perm_second_derivative_odd_exists_witnesses_sigma_fn,
           perm_second_derivative_odd_exists_witnesses_sigma_val] at hval
    omega
  · intro h
    have h0 : perm_second_derivative_odd_exists_witnesses_pi_perm k ⟨0, by omega⟩ = ⟨0, by omega⟩ := by rw [h]; rfl
    have hval := congr_arg Fin.val h0
    dsimp [perm_second_derivative_odd_exists_witnesses_pi_perm,
           perm_second_derivative_odd_exists_witnesses_pi_fn,
           perm_second_derivative_odd_exists_witnesses_pi_val] at hval
    omega
  · intro h
    have h0 : perm_second_derivative_odd_exists_witnesses_pi_perm k ⟨0, by omega⟩ = Fin.revPerm ⟨0, by omega⟩ := by rw [h]
    have hval := congr_arg Fin.val h0
    have hr : ((Fin.revPerm (⟨0, by omega⟩ : Fin (2 * k + 1))) : Fin (2 * k + 1)).val = 2 * k := by
      rw [Fin.revPerm_apply, Fin.val_rev]; rfl
    rw [hr] at hval
    dsimp [perm_second_derivative_odd_exists_witnesses_pi_perm,
           perm_second_derivative_odd_exists_witnesses_pi_fn,
           perm_second_derivative_odd_exists_witnesses_pi_val] at hval
    omega
  · funext ℓ
    unfold perm_second_derivative
    split_ifs with h
    · dsimp [perm_second_derivative_odd_exists_witnesses_sigma_perm,
             perm_second_derivative_odd_exists_witnesses_pi_perm,
             perm_second_derivative_odd_exists_witnesses_sigma_fn,
             perm_second_derivative_odd_exists_witnesses_pi_fn]
      unfold perm_second_derivative_odd_exists_witnesses_sigma_val
             perm_second_derivative_odd_exists_witnesses_pi_val
      split_ifs <;> omega
    · rfl
