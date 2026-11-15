import AFTD.Prelude

/-!
# ose_hamming_antipode

Topic: algorithms   Node: 4b2e26170801

Provenance: helper lemma. arXiv:2611.08546, Section 6.1; Boolean-cube distortion argument

Every Boolean n-tuple differs from its bitwise complement in exactly n coordinates.
-/

theorem ose_hamming_antipode (n : ℕ) (x : Fin n → Bool) :
    hammingDist x (fun i => !(x i)) = n := by
  classical
  have h (i : Fin n) : x i ≠ !(x i) := by cases hxi : x i <;> simp [hxi]
  simp [hammingDist, h]
