import AFTD.Prelude

/-!
# is_k_submod_kernel

Topic: submodular   Node: dc2c22dad1c8

Provenance: formalization of a published result. Source: arXiv:2610.26677, Lemma 2.1

A two-variable kernel H : ℝ → ℝ → ℝ satisfies the hidden-label conditions if H(0,0) = 0, H(1,0) > 0, H(x,y) ≤ H(1,0) on [0,1]², H is coordinatewise nondecreasing on [0,1]², and each first partial derivative of H is coordinatewise nonincreasing on [0,1]².
-/

/-- Kernel conditions: H(0,0)=0, H(1,0)>0, bounded by H(1,0), coordinatewise nondecreasing, and coordinatewise nonincreasing first partial derivatives on [0,1]^2. -/
def is_k_submod_kernel (H : ℝ → ℝ → ℝ) : Prop :=
  H 0 0 = 0 ∧
  0 < H 1 0 ∧
  (∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → H x y ≤ H 1 0) ∧
  (∀ x₁ x₂ y, 0 ≤ x₁ → x₁ ≤ x₂ → x₂ ≤ 1 → 0 ≤ y → y ≤ 1 → H x₁ y ≤ H x₂ y) ∧
  (∀ x y₁ y₂, 0 ≤ x → x ≤ 1 → 0 ≤ y₁ → y₁ ≤ y₂ → y₂ ≤ 1 → H x y₁ ≤ H x y₂) ∧
  (∀ x₁ x₂ y₁ y₂, 0 ≤ x₁ → x₁ ≤ x₂ → x₂ ≤ 1 → 0 ≤ y₁ → y₁ ≤ y₂ → y₂ ≤ 1 →
    deriv (fun t => H t y₂) x₂ ≤ deriv (fun t => H t y₁) x₁) ∧
  (∀ x₁ x₂ y₁ y₂, 0 ≤ x₁ → x₁ ≤ x₂ → x₂ ≤ 1 → 0 ≤ y₁ → y₁ ≤ y₂ → y₂ ≤ 1 →
    deriv (fun t => H x₂ t) y₂ ≤ deriv (fun t => H x₁ t) y₁)
