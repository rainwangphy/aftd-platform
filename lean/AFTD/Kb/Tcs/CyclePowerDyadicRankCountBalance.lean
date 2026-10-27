import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent

/-!
# cycle_power_dyadic_rank_count_balance

Topic: combinatorics   Node: 207918040827

Provenance: helper lemma. Uniform structural helper for OP-205 / RT-1 following arXiv:2610.15635 Section 3. This exact rank-flow identity is a helper, not a new graph covering theorem or research advance.

At every nontrivial dyadic tree rank, exact long-edge coverage is a two-term occupancy balance L_j(v)+R_j(v+D-2^j)=1, uniformly in the radius. Each term is therefore at most one.
-/

open Finset

theorem cycle_power_dyadic_rank_count_balance
    (m j : ℕ) (hj : 1 ≤ j) (hjm : j < m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (range (2 ^ m)).sum (fun a => (x p a).toNat))
    (hexact : ∀ v : ℤ, (range (2 ^ j)).sum (fun a =>
      (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 ^ m - 2 ^ j)).toNat) = 1) :
    ∀ v : ℤ,
      (range (2 ^ (j - 1))).sum (fun a =>
        (x (v - ((2 ^ (j - 1) + a : ℕ) : ℤ)) (2 ^ (j - 1) + a)).toNat) +
      (range (2 ^ (j - 1))).sum (fun a =>
        (x (v + ((2 ^ m - 2 ^ j : ℕ) : ℤ) -
          ((2 ^ m - 2 ^ j + a : ℕ) : ℤ)) (2 ^ m - 2 ^ j + a)).toNat) = 1 := by
  intro v
  let q := 2 ^ (j - 1)
  let d := 2 ^ m - 2 ^ j
  have hpow : 2 ^ j = q + q := by
    have he : j = (j - 1) + 1 := by omega
    rw [he, pow_succ]
    dsimp [q]
    omega
  have hdm : 2 ^ j ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
  have hp := fun p => cycle_power_dyadic_tight_class_parent m j hj hjm (x p) (htight p)
  have he := hexact v
  rw [hpow, sum_range_add] at he
  have hlow : (range q).sum (fun a =>
      (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 ^ m - (q + q))).toNat) =
      (range q).sum (fun a =>
        (x (v + (d : ℤ) - ((d + a : ℕ) : ℤ)) (d + a)).toNat) := by
    apply sum_congr rfl
    intro a ha
    have haq : a < q := mem_range.mp ha
    have hp' := (hp (v - (a : ℤ)) a (by omega)).1 haq
    have hi : a + 2 ^ m - 2 ^ j = d + a := by dsimp [d]; omega
    have hi' : a + 2 ^ m - (q + q) = d + a := by dsimp [d]; omega
    have hv : v + (d : ℤ) - ((d + a : ℕ) : ℤ) = v - (a : ℤ) := by push_cast; ring
    rw [hi] at hp'
    rw [hi', hv]
    cases hb : x (v - (a : ℤ)) (d + a)
    · simp [hb]
    · simp [hb, hp' hb]
  have hhigh : (range q).sum (fun a =>
      (x (v - ((q + a : ℕ) : ℤ)) (q + a) &&
        x (v - ((q + a : ℕ) : ℤ)) (q + a + 2 ^ m - (q + q))).toNat) =
      (range q).sum (fun a => (x (v - ((q + a : ℕ) : ℤ)) (q + a)).toNat) := by
    apply sum_congr rfl
    intro a ha
    have haq : a < q := mem_range.mp ha
    have hp' := (hp (v - ((q + a : ℕ) : ℤ)) (q + a) (by omega)).2 (by omega)
    have hi : q + a + 2 ^ m - (q + q) = q + a + 2 ^ m - 2 ^ j := by omega
    rw [hi]
    cases hb : x (v - ((q + a : ℕ) : ℤ)) (q + a)
    · simp [hb]
    · simpa only [Bool.true_and] using congrArg Bool.toNat (hp' hb)
  rw [hlow, hhigh] at he
  change (range q).sum (fun a => (x (v - ((q + a : ℕ) : ℤ)) (q + a)).toNat) +
    (range q).sum (fun a => (x (v + (d : ℤ) - ((d + a : ℕ) : ℤ)) (d + a)).toNat) = 1
  omega
