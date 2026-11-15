import AFTD.Prelude

/-!
# ose_hamming_flip

Topic: algorithms   Node: 44c51fe2e2d3

Provenance: helper lemma. arXiv:2611.08546, Section 6.1; Boolean-cube distortion argument

A Boolean tuple and the tuple obtained by flipping one coordinate have Hamming distance one.
-/

theorem ose_hamming_flip (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    hammingDist x (Function.update x i (!(x i))) = 1 := by
  classical
  have hset : (Finset.univ.filter fun j : Fin n => x j ≠ Function.update x i (!(x i)) j) = {i} := by
    ext j
    by_cases h : j = i
    · subst j
      cases hxi : x i <;> simp [Function.update, hxi]
    · simp [Function.update, h]
  simp [hammingDist, hset]
