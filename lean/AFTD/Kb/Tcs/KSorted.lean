import AFTD.Prelude

/-!
# k_sorted

Topic: algorithms   Node: b576de6c66a5

Provenance: formalization of a published result. Source: arXiv:2611.27671 "Shellsort with O(n log n) Average-Case Complexity", Section 2.1

An array $A : \text{Fin } n \to \alpha$ is $k$-sorted if $A_i \le A_{i+k}$ whenever $i+k < n$.
-/

/-- An array is k-sorted if elements at distance k are in non-decreasing order. -/
def k_sorted {n : ℕ} (k : ℕ) {α : Type*} [Preorder α] (A : Fin n → α) : Prop := ∀ (i : Fin n) (hi : i.val + k < n), A i ≤ A ⟨i.val + k, hi⟩
