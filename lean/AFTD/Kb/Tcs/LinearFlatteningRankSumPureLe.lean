import AFTD.Prelude
import AFTD.Kb.Tcs.Tensor3Pure

/-!
# linear_flattening_rank_sum_pure_le

Topic: algebraic_complexity   Node: 9fc9fc82ff39

Provenance: formalization of a published result. Source: arXiv:2610.08504 (Explicit tensors beyond the linear flattening barrier), Sec. 1 (the linear flattening method: Pot(L) > r gives nontrivial equations for σ_r); rank version, without the closure step to border rank

If rank L(x ⊗ y ⊗ z) ≤ ρ for all x, y, z, then rank L(T) ≤ r ρ for every sum T of r pure tensors; this is why potency greater than r yields equations for tensors of rank at most r.
-/

lemma linear_flattening_rank_sum_pure_le_rank_add {u v : ℕ} (A B : Matrix (Fin u) (Fin v) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  dsimp [Matrix.rank]
  rw [Matrix.mulVecLin_add]
  have h_le : LinearMap.range (Matrix.mulVecLin A + Matrix.mulVecLin B) ≤
      LinearMap.range (Matrix.mulVecLin A) ⊔ LinearMap.range (Matrix.mulVecLin B) :=
    LinearMap.range_add_le _ _
  have h_mono := Submodule.finrank_mono h_le
  exact h_mono.trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma linear_flattening_rank_sum_pure_le_rank_sum {ι : Type*} {u v : ℕ}
    (s : Finset ι) (F : ι → Matrix (Fin u) (Fin v) ℂ) :
    (∑ i ∈ s, F i).rank ≤ ∑ i ∈ s, (F i).rank := by
  induction s using Finset.cons_induction with
  | empty =>
    simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    have h_add := linear_flattening_rank_sum_pure_le_rank_add (F a) (∑ i ∈ s, F i)
    exact h_add.trans (Nat.add_le_add_left ih _)

theorem linear_flattening_rank_sum_pure_le {n u v : ℕ}
    (L : (Fin n → Fin n → Fin n → ℂ) →ₗ[ℂ] Matrix (Fin u) (Fin v) ℂ) (ρ : ℕ)
    (hρ : ∀ x y z : Fin n → ℂ, (L (tensor3_pure x y z)).rank ≤ ρ)
    (r : ℕ) (x y z : Fin r → Fin n → ℂ) :
    (L (∑ i, tensor3_pure (x i) (y i) (z i))).rank ≤ r * ρ := by
  rw [map_sum]
  have h1 : (∑ i, L (tensor3_pure (x i) (y i) (z i))).rank ≤
      ∑ i, (L (tensor3_pure (x i) (y i) (z i))).rank :=
    linear_flattening_rank_sum_pure_le_rank_sum Finset.univ _
  have h2 : ∑ i : Fin r, (L (tensor3_pure (x i) (y i) (z i))).rank ≤
      ∑ _i : Fin r, ρ :=
    Finset.sum_le_sum (fun i _ => hρ (x i) (y i) (z i))
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at h2
  exact h1.trans h2
