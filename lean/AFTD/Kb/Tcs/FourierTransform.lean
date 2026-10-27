import AFTD.Prelude

/-!
# fourier_transform

Topic: combinatorics   Node: d46866495a71

Provenance: formalization of a published result. Source: arXiv:2610.31807, equation (2.1)

The normalized Fourier transform of a complex-valued function $f : H \to \mathbb{C}$ on a finite additive abelian group $H$ (`AddCommGroup H` with `Fintype H`), defined for an additive character $\gamma : \operatorname{AddChar} H\ \mathbb{C}$ as $(\sqrt{|H|})^{-1} \sum_{x \in H} f(x) \overline{\gamma(x)}$, where $|H| = \operatorname{card}(H)$ and the square root is inverted in $\mathbb{C}$.
-/

/-- Normalized Fourier transform of a complex-valued function on a finite additive abelian group. -/
noncomputable def fourier_transform {H : Type*} [AddCommGroup H] [Fintype H]
    (f : H → ℂ) (γ : AddChar H ℂ) : ℂ := (Real.sqrt (Fintype.card H) : ℂ)⁻¹ * ∑ x : H, f x * star (γ x)
