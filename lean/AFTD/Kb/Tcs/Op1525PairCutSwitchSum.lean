import AFTD.Prelude

/-!
# op1525_pair_cut_switch_sum

Topic: combinatorics   Node: c4215ff0ed6a

Provenance: helper lemma. A component of the complete-multipartite reconstruction route for OP-1525 and arXiv:2611.13901.

For any finite collection of ordered nonloop vertex pairs and a Boolean vertex coloring, the sum over all single-vertex switches of the number of differently colored pairs equals (n−4) times the original number plus twice the number of pairs.
-/

theorem op1525_pair_cut_switch_sum
    {V : Type*} [DecidableEq V] [Fintype V]
    (E : Finset (V × V)) (f : V → Bool)
    (hloop : ∀ e ∈ E, e.1 ≠ e.2) :
    (∑ v : V, ∑ e ∈ E,
      if xor (f e.1) (decide (e.1 = v)) = xor (f e.2) (decide (e.2 = v))
      then (0 : ℤ) else 1) =
      ((Fintype.card V : ℤ) - 4) *
        (∑ e ∈ E, if f e.1 = f e.2 then (0 : ℤ) else 1) +
        2 * (E.card : ℤ) := by
  classical
  rw [Finset.sum_comm]
  have hsingle (e : V × V) (he : e ∈ E) :
      (∑ v : V,
        if xor (f e.1) (decide (e.1 = v)) = xor (f e.2) (decide (e.2 = v))
        then (0 : ℤ) else 1) =
      ((Fintype.card V : ℤ) - 4) *
        (if f e.1 = f e.2 then (0 : ℤ) else 1) + 2 := by
    let c : ℤ := if f e.1 = f e.2 then 0 else 1
    have hpoint (v : V) :
        (if xor (f e.1) (decide (e.1 = v)) = xor (f e.2) (decide (e.2 = v))
         then (0 : ℤ) else 1) =
        c + (if e.1 = v then 1 - 2 * c else 0) +
          (if e.2 = v then 1 - 2 * c else 0) := by
      have hne := hloop e he
      by_cases h1 : e.1 = v <;> by_cases h2 : e.2 = v <;>
        cases ha : f e.1 <;> cases hb : f e.2 <;>
        simp_all [c] <;> omega
    have hsum (a : V) (z : ℤ) : (∑ v : V, if a = v then z else 0) = z := by
      simp [eq_comm]
    simp_rw [hpoint, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hsum, hsum]
    dsimp [c]
    ring
  calc
    _ = ∑ e ∈ E, (((Fintype.card V : ℤ) - 4) *
        (if f e.1 = f e.2 then (0 : ℤ) else 1) + 2) := by
          apply Finset.sum_congr rfl
          intro e he
          exact hsingle e he
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp [mul_comm]
