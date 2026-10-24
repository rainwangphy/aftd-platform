import AFTD.Prelude

/-!
# koszul_flattening

Topic: algebraic_complexity   Node: 17aa1bee8650

Provenance: helper lemma. step towards linear_flattening_testable_order_gap_two

The Koszul flattening K_p on (ℂⁿ)⊗³: rows are indexed by a (p+1)-subset J of Fin n together with a vector index k, columns by a p-subset I together with an index j, and the entry at ((J,k),(I,j)) is the alternating sum over i with J = insert i I of (-1)^(number of elements of I below i) times T_{ijk}.
-/

/-- The Koszul flattening K_p: the matrix of the map ω ⊗ φ ↦ Σ_{i,j,k} T_{ijk} (e_i ∧ ω) ⊗ φ(e_j)e_k from Λ^p ℂⁿ ⊗ (ℂⁿ)* to Λ^{p+1} ℂⁿ ⊗ ℂⁿ, written in the monomial basis of the exterior powers. -/
noncomputable def koszul_flattening (n p : ℕ) :
    (Fin n → Fin n → Fin n → ℂ) →ₗ[ℂ]
      Matrix ({J : Finset (Fin n) // J.card = p + 1} × Fin n)
        ({I : Finset (Fin n) // I.card = p} × Fin n) ℂ where
  toFun T := Matrix.of (fun r c => ∑ i : Fin n, if r.1.1 = insert i c.1.1 then ((-1 : ℂ) ^ (c.1.1.filter (fun x => x < i)).card) * T i c.2 r.2 else 0)
  map_add' T T' := by
      ext r c
      rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      split_ifs with h <;> simp [mul_add]
  map_smul' a T := by
      ext r c
      rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      split_ifs with h
      · simp only [RingHom.id_apply]; ring
      · ring
