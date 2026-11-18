import AFTD.Prelude
import AFTD.Kb.Tcs.Op861ThirdRootsSubsetSumNorm

/-!
# op861_order_three_character_sum_bound

Topic: graphs   Node: 7a3485279040

Provenance: helper lemma. Translation-orbit estimate used in op861_ternary_crossing_pairs_dense.

In a finite abelian group in which three times every element is zero, every nontrivial complex additive character has a sum of norm at most one third of the group order over any finite subset.
-/

open scoped BigOperators

theorem op861_order_three_character_sum_bound (G : Type*) [AddCommGroup G]
    [Fintype G] [DecidableEq G] (h3 : ∀ t : G, t+t+t = 0)
    (χ : AddChar G ℂ) (hχ : χ ≠ 0) (S : Finset G) :
    3 * ‖∑ x ∈ S, χ x‖ ≤ (Fintype.card G : ℝ) := by
  classical
  have ht : ∃ t : G, χ t ≠ 1 := by
    by_contra! h
    apply hχ
    ext t
    simpa using h t
  obtain ⟨t, ht⟩ := ht
  have hpow : (χ t)^3 = 1 := by
    simpa [AddChar.map_add_eq_mul, pow_succ, mul_assoc] using congrArg χ (h3 t)
  let w : G → ℂ := fun x => if x ∈ S then χ x else 0
  let v : G → ℂ := fun x => w x + w (x+t) + w (x+(t+t))
  have htrans (a : G) : (∑ x : G, w (x+a)) = ∑ x : G, w x := by
    exact Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)
  have hw : (∑ x : G, w x) = ∑ x ∈ S, χ x := by
    simp [w]
  have hv (x : G) : ‖v x‖ ≤ 1 := by
    let a : Bool := decide (x ∈ S)
    let b : Bool := decide (x+t ∈ S)
    let c : Bool := decide (x+(t+t) ∈ S)
    have hb := op861_third_roots_subset_sum_norm (χ t) hpow ht (χ.norm_apply t) a b c
    have heq : v x = χ x * ((if a then (1 : ℂ) else 0) + (if b then χ t else 0) + (if c then (χ t)^2 else 0)) := by
      dsimp [v, w, a, b, c]
      simp only [AddChar.map_add_eq_mul, pow_two]
      split_ifs <;> simp_all <;> ring
    rw [heq, norm_mul, χ.norm_apply, one_mul]
    exact hb
  have hsum : (∑ x : G, v x) = (3 : ℂ) * ∑ x ∈ S, χ x := by
    simp only [v, Finset.sum_add_distrib, htrans, hw]
    ring
  calc
    3 * ‖∑ x ∈ S, χ x‖ = ‖(3 : ℂ) * ∑ x ∈ S, χ x‖ := by simp
    _ = ‖∑ x : G, v x‖ := by rw [hsum]
    _ ≤ ∑ x : G, ‖v x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : G, (1 : ℝ) := Finset.sum_le_sum fun x hx => hv x
    _ = (Fintype.card G : ℝ) := by simp
