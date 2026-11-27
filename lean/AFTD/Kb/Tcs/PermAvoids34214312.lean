import AFTD.Prelude

/-!
# perm_avoids_3421_4312

Topic: combinatorics   Node: cdcb19aae7e8

Provenance: formalization of a published result. Source: arXiv:2611.33575 Section 8

A permutation $\sigma$ on $\{0, \dots, n-1\}$ avoids both classical patterns 3421 and 4312: there are no four indices $i_1 < i_2 < i_3 < i_4$ whose values are ordered as $\sigma(i_4) < \sigma(i_3) < \sigma(i_1) < \sigma(i_2)$ or as $\sigma(i_3) < \sigma(i_4) < \sigma(i_2) < \sigma(i_1)$.
-/

/-- Predicate for a permutation on Fin n avoiding both patterns 3421 and 4312. -/
def perm_avoids_3421_4312 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop := (∀ ⦃i₁ i₂ i₃ i₄ : Fin n⦄, i₁ < i₂ → i₂ < i₃ → i₃ < i₄ → ¬ (σ i₄ < σ i₃ ∧ σ i₃ < σ i₁ ∧ σ i₁ < σ i₂)) ∧
  (∀ ⦃i₁ i₂ i₃ i₄ : Fin n⦄, i₁ < i₂ → i₂ < i₃ → i₃ < i₄ → ¬ (σ i₃ < σ i₄ ∧ σ i₄ < σ i₂ ∧ σ i₂ < σ i₁))
