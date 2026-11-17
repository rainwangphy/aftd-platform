import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op1525_multipartite_profile_card_injective

Topic: combinatorics   Node: 5b02380c91f9

Provenance: helper lemma. The decisive profile-recovery step in the multipartite route for OP-1525.

If two integer profiles of equally sized blocks differ by the difference of two adjacent one-block transitions, and their quadratic mixed-pair scores agree, then the profiles are equal.
-/

theorem op1525_multipartite_profile_card_injective (r : ℕ) (i j : Fin r)
    (f g : Fin (r + 1) → ℤ)
    (hchange : ∀ k : Fin (r + 1), f k - g k =
      ((if k = i.castSucc then 1 else 0) - (if k = i.succ then 1 else 0)) -
      ((if k = j.castSucc then 1 else 0) - (if k = j.succ then 1 else 0)))
    (hscore : ∑ k : Fin (r + 1), f k * (k.val : ℤ) * ((r : ℤ) - k.val) =
      ∑ k : Fin (r + 1), g k * (k.val : ℤ) * ((r : ℤ) - k.val)) : f = g := by
  classical
  have he : (∑ k : Fin (r + 1), (f k - g k) * (k.val : ℤ) * ((r : ℤ) - k.val)) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    linarith
  simp_rw [hchange] at he
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one] at he
  have hij : (i.val : ℤ) = (j.val : ℤ) := by nlinarith
  have hij' : i = j := Fin.ext (Int.ofNat.inj hij)
  subst j
  funext k
  have hk := hchange k
  simp only [sub_self] at hk
  linarith
