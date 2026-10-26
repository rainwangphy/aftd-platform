import AFTD.Prelude
import AFTD.Kb.Tcs.Gf8OracleTCountGe20
import AFTD.Kb.Tcs.Monomial

/-!
# monomial_mul

Topic: information   Node: 4488d837604d

Provenance: helper lemma. arXiv:2610.29807, Lemma 3.2: Some Results on the Weight Spectrum of Binary Reed-Muller Codes RM(m-7,m)

For any natural number s and any two finite subsets I and J of Fin s, the pointwise product of the coordinate monomials monomial I and monomial J on (Fin s → ZMod 2) to ZMod 2 is equal to the coordinate monomial monomial (I ∪ J).
-/

lemma monomial_mul_zmod2_mul_self (a : ZMod 2) : a * a = a := by
  rcases gf8_zmod2_cases a with rfl | rfl <;> ring

lemma monomial_mul_prod_mul_mem {s : ℕ} (I : Finset (Fin s)) (a : Fin s) (ha : a ∈ I) (x : Fin s → ZMod 2) :
    (∏ i ∈ I, x i) * x a = ∏ i ∈ I, x i := by
  conv_lhs => rw [← Finset.insert_erase ha]
  rw [Finset.prod_insert (Finset.notMem_erase a I)]
  have : (x a * ∏ i ∈ I.erase a, x i) * x a = (x a * x a) * ∏ i ∈ I.erase a, x i := by ring
  rw [this, monomial_mul_zmod2_mul_self]
  rw [← Finset.prod_insert (Finset.notMem_erase a I), Finset.insert_erase ha]

/-- The pointwise product of two coordinate monomials is the monomial of their union. -/
theorem monomial_mul {s : ℕ} (I J : Finset (Fin s)) :
    (monomial I * monomial J : (Fin s → ZMod 2) → ZMod 2) = monomial (I ∪ J) := by
  ext x
  dsimp [monomial]
  induction J using Finset.induction_on with
  | empty => simp
  | @insert a s' ha ih =>
    rw [Finset.prod_insert ha]
    by_cases haI : a ∈ I
    · rw [← Finset.insert_union_comm, Finset.insert_eq_of_mem haI]
      calc (∏ i ∈ I, x i) * (x a * ∏ i ∈ s', x i)
        _ = ((∏ i ∈ I, x i) * x a) * ∏ i ∈ s', x i := by ring
        _ = (∏ i ∈ I, x i) * ∏ i ∈ s', x i := by rw [monomial_mul_prod_mul_mem I a haI x]
        _ = ∏ i ∈ I ∪ s', x i := ih
    · rw [← Finset.insert_union_comm, Finset.insert_union]
      have ha_union : a ∉ I ∪ s' := by
        rw [Finset.mem_union]
        intro h
        cases h with
        | inl h1 => exact haI h1
        | inr h2 => exact ha h2
      rw [Finset.prod_insert ha_union]
      calc (∏ i ∈ I, x i) * (x a * ∏ i ∈ s', x i)
        _ = x a * ((∏ i ∈ I, x i) * ∏ i ∈ s', x i) := by ring
        _ = x a * (∏ i ∈ I ∪ s', x i) := by rw [ih]
