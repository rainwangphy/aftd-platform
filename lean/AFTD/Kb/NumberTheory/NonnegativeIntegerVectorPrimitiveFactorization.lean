import AFTD.Prelude

/-!
# nonnegative_integer_vector_primitive_factorization

Topic: elementary_number_theory   Node: 9f0bcc882605

Provenance: helper lemma. Supporting lemma or explicit route obstruction for OP-197 / arXiv:2610.16562 Conjecture1, deep session2. The abstract two-ray fact and finite obstruction are not claimed novel or research-level; no part is the full box conjecture. The five-point kernel has columns (1,1),(1,0),(0,1),(-2,0),(0,-2).

Every nonzero nonnegative finite integer vector u equals d*v coordinatewise for a positive natural d and a nonzero nonnegative integer vector v whose only common natural coordinate divisors divide one.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem nonnegative_integer_vector_primitive_factorization {ι : Type*} [Fintype ι]
    (u : ι → ℤ) (hu : ∀ i, 0 ≤ u i) (hne : u ≠ 0) :
    ∃ (d : ℕ) (v : ι → ℤ), 0 < d ∧ (∀ i, 0 ≤ v i) ∧ v ≠ 0 ∧
      (∀ i, u i = (d : ℤ)*v i) ∧
      (∀ e : ℕ, (∀ i, (e : ℤ) ∣ v i) → e ∣ 1) := by
  classical
  have hex : ∃ i, u i ≠ 0 := by
    by_contra hh; push_neg at hh
    exact hne (funext hh)
  obtain ⟨i,hi⟩ := hex
  let f := fun i => (u i).toNat
  have hfu : ∀ i, (f i : ℤ) = u i := by intro i; exact Int.toNat_of_nonneg (hu i)
  have hfi : f i ≠ 0 := by intro hh; have hh' := hfu i; rw [hh] at hh'; simp only [Nat.cast_zero] at hh'; exact hi hh'.symm
  obtain ⟨v,hfac,hgcd⟩ := Finset.extract_gcd (s:=Finset.univ) f ⟨i,Finset.mem_univ i⟩
  let d := Finset.univ.gcd f
  have hd : 0 < d := by
    have hh := hfac i (Finset.mem_univ i)
    by_contra hn
    have hz : d=0 := by omega
    change f i=d*v i at hh
    rw [hz,zero_mul] at hh
    exact hfi hh
  let z := fun i => (v i : ℤ)
  have hfacz : ∀ i, u i=(d : ℤ)*z i := by
    intro k
    have hh := hfac k (Finset.mem_univ k)
    have hh' : (f k : ℤ)=(d : ℤ)*z k := by
      change (f k : ℤ)=(d : ℤ)*(v k : ℤ)
      change f k=d*v k at hh
      exact_mod_cast hh
    rwa [hfu k] at hh'
  have hzne : z ≠ 0 := by
    intro hh
    apply hne
    funext k
    have hk := hfacz k
    have hzk := congrFun hh k
    simp only [Pi.zero_apply] at hzk
    simpa [hzk] using hk
  refine ⟨d,z,hd,?_,hzne,hfacz,?_⟩
  · intro k; exact Nat.cast_nonneg _
  · intro e he
    have hdiv : e ∣ Finset.univ.gcd v := by
      apply Finset.dvd_gcd
      intro k hk
      have hh := he k
      change (e : ℤ) ∣ (v k : ℤ) at hh
      exact_mod_cast hh
    simpa only [hgcd] using hdiv
