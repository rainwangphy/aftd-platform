import AFTD.Prelude
import AFTD.Kb.NumberTheory.FourPointPositiveKernelBoundaryDecomposition
import AFTD.Kb.NumberTheory.NonnegativeIntegerVectorPrimitiveFactorization
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# four_point_positive_kernel_primitive_boundary_decomposition

Topic: elementary_number_theory   Node: af82fed95fea

Provenance: helper lemma. Supporting lemma or explicit route obstruction for OP-197 / arXiv:2610.16562 Conjecture1, deep session2. The abstract two-ray fact and finite obstruction are not claimed novel or research-level; no part is the full box conjecture. The five-point kernel has columns (1,1),(1,0),(0,1),(-2,0),(0,-2).

For two integer rows on four coordinates with independent first two columns and a strictly positive integer common kernel vector x, there are two nonzero nonnegative primitive integer common kernel vectors u,v, each having a zero coordinate, and positive integer D,c,d (represented in Z) such that D*x=c*u+d*v. This constructs the primitive boundary decomposition but does not yet prove their minimal-zero-sum interpretation or the box three-support length bound.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem four_point_positive_kernel_primitive_boundary_decomposition
    (a b x : Fin 4 → ℤ) (hx : ∀ i, 0 < x i)
    (hxa : (∑ i, x i*a i) = 0) (hxb : (∑ i, x i*b i) = 0)
    (hind : a 0*b 1 - a 1*b 0 ≠ 0) :
    ∃ (u v : Fin 4 → ℤ) (i j : Fin 4) (D c d : ℤ),
      (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k) ∧ u ≠ 0 ∧ v ≠ 0 ∧
      u i = 0 ∧ v j = 0 ∧ 0 < D ∧ 0 < c ∧ 0 < d ∧
      (∀ k, D*x k = c*u k + d*v k) ∧
      (∑ k, u k*a k) = 0 ∧ (∑ k, u k*b k) = 0 ∧
      (∑ k, v k*a k) = 0 ∧ (∑ k, v k*b k) = 0 ∧
      (∀ e : ℕ, (∀ k, (e : ℤ) ∣ u k) → e ∣ 1) ∧
      (∀ e : ℕ, (∀ k, (e : ℤ) ∣ v k) → e ∣ 1) := by
  obtain ⟨u0,v0,i,j,D,c,d,hu0,hv0,hun0,hvn0,hui0,hvj0,hD,hc,hd,hrel,hua0,hub0,hva0,hvb0⟩ :=
    four_point_positive_kernel_boundary_decomposition a b x hx hxa hxb hind
  obtain ⟨g,u,hg,hu,hun,hgu,hpu⟩ := nonnegative_integer_vector_primitive_factorization u0 hu0 hun0
  obtain ⟨h,v,hh,hv,hvn,hhv,hpv⟩ := nonnegative_integer_vector_primitive_factorization v0 hv0 hvn0
  have hgz : (0 : ℤ)<g := by exact_mod_cast hg
  have hhz : (0 : ℤ)<h := by exact_mod_cast hh
  have hker (z0 z : Fin 4 → ℤ) (t : ℕ) (ht : 0<t)
      (hfac : ∀ k, z0 k=(t : ℤ)*z k) (r : Fin 4 → ℤ)
      (hz0 : (∑ k, z0 k*r k)=0) : (∑ k, z k*r k)=0 := by
    have he : (t : ℤ)*(∑ k,z k*r k)=0 := by
      calc
        _ = ∑ k,z0 k*r k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk; rw [hfac k]; ring
        _ = 0 := hz0
    exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast ht.ne')
  have hui : u i=0 := by
    have he := hgu i
    rw [hui0] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hgz.ne'
  have hvj : v j=0 := by
    have he := hhv j
    rw [hvj0] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hhz.ne'
  refine ⟨u,v,i,j,D,c*(g : ℤ),d*(h : ℤ),hu,hv,hun,hvn,hui,hvj,hD,
    mul_pos hc hgz,mul_pos hd hhz,?_,
    hker u0 u g hg hgu a hua0,hker u0 u g hg hgu b hub0,
    hker v0 v h hh hhv a hva0,hker v0 v h hh hhv b hvb0,hpu,hpv⟩
  intro k
  rw [hrel k,hgu k,hhv k]
  ring
