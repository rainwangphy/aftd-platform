import AFTD.Prelude
import AFTD.Kb.Tcs.TwistedFrobeniusMap
import AFTD.Kb.Tcs.TwistedFrobeniusInv

/-!
# finite_field_rectangle_twisted_frobenius_degenerate

Topic: combinatorics   Node: ba0dae51c5da

Provenance: helper lemma. scout/2611-17378-a-19-5-lower-bound-for-the-four-dimensional-erd-h-o-s-box-p.md:154

Let $k$ be a finite field of characteristic 2 and $K$ a degree-3 field extension of $k$. Let $q = |k|$ and $A_{ij} = Q^{-1}(u_i + v_j)$. If $u_0 = u_1$ or $v_0 = v_1$, then $\sum_{i,j} A_{ij} = 0$ and $\sum_{i,j} \operatorname{Tr}(u_i A_{ij}) = 0$.
-/

/-- Degenerate case of Lemma 2: if u0 = u1 or v0 = v1, both sums vanish. -/
theorem finite_field_rectangle_twisted_frobenius_degenerate
    (k K : Type*) [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K] [FiniteDimensional k K] [CharP k 2]
    (hrank : Module.finrank k K = 3)
    (u v : Fin 2 → K)
    (hdeg : u 0 = u 1 ∨ v 0 = v 1) :
    let q := Fintype.card k
    let A : Fin 2 → Fin 2 → K := fun i j => twisted_frobenius_inv q (u i + v j)
    (∑ i, ∑ j, A i j) = 0 ∧ (∑ i, ∑ j, Algebra.trace k K (u i * A i j)) = 0 := by
  intro q A
  have : CharP K 2 := (Algebra.charP_iff k K 2).mp ‹CharP k 2›
  have hsum_A : (∑ i, ∑ j, A i j) = A 0 0 + A 0 1 + (A 1 0 + A 1 1) := by
    simp only [Fin.sum_univ_two]
  have hsum_tr : (∑ i, ∑ j, Algebra.trace k K (u i * A i j)) =
      Algebra.trace k K (u 0 * A 0 0) + Algebra.trace k K (u 0 * A 0 1) +
      (Algebra.trace k K (u 1 * A 1 0) + Algebra.trace k K (u 1 * A 1 1)) := by
    simp only [Fin.sum_univ_two]
  rcases hdeg with hu | hv
  · have h0 : A 0 0 = A 1 0 := by dsimp [A]; rw [hu]
    have h1 : A 0 1 = A 1 1 := by dsimp [A]; rw [hu]
    constructor
    · rw [hsum_A, h0, h1]
      exact CharTwo.add_self_eq_zero (A 1 0 + A 1 1)
    · rw [hsum_tr, hu, h0, h1]
      exact CharTwo.add_self_eq_zero (Algebra.trace k K (u 1 * A 1 0) + Algebra.trace k K (u 1 * A 1 1))
  · have h0 : A 0 0 = A 0 1 := by dsimp [A]; rw [hv]
    have h1 : A 1 0 = A 1 1 := by dsimp [A]; rw [hv]
    constructor
    · rw [hsum_A, h0, h1]
      rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    · rw [hsum_tr, h0, h1]
      rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
