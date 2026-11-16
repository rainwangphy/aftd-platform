import AFTD.Prelude

/-!
# phi_cubed_eq_self_of_zero_sum

Topic: combinatorics   Node: b4918eb582df

Provenance: helper lemma. arXiv:2611.18059 Proposition 3.1 proof

Let Γ be an additive Abelian group and φ a permutation of Γ satisfying x + φ(x) + φ²(x) = 0 for all x. Then φ³(x) = x for all x.
-/

/-- Applying the zero-sum condition x + φ(x) + φ²(x) = 0 at x and φ(x) implies φ³(x) = x. -/
theorem phi_cubed_eq_self_of_zero_sum {Γ : Type*} [AddCommGroup Γ] (φ : Equiv.Perm Γ)
    (h_sum : ∀ x : Γ, x + φ x + φ (φ x) = 0) (x : Γ) :
    φ (φ (φ x)) = x := by
  have h1 := h_sum x
  have h2 := h_sum (φ x)
  have h3 : φ (φ (φ x)) - x = (φ x + φ (φ x) + φ (φ (φ x))) - (x + φ x + φ (φ x)) := by
    abel
  rw [h2, h1, sub_zero] at h3
  exact sub_eq_zero.mp h3
