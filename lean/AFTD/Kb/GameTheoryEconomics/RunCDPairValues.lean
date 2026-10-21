import AFTD.Prelude

/-!
# run_C_D_pair_values

Topic: combinatorial_games   Node: acfc5e3e5abd

Provenance: helper lemma. scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md:445

For every integer h ≥ 1, the pair consisting of h mod 2 and the indicator of (h ≥ 2 and h is even) is either (0, 1) or (1, 0).
-/

/-- For all h ≥ 1, the Grundy values C_h and D_h form the set {0, 1}. -/
theorem run_C_D_pair_values (h : ℕ) (hh : 1 ≤ h) :
    (h % 2 = 0 ∧ (if h ≥ 2 ∧ Even h then 1 else 0) = 1) ∨
    (h % 2 = 1 ∧ (if h ≥ 2 ∧ Even h then 1 else 0) = 0) := by
  by_cases he : Even h
  · left
    constructor
    · exact Nat.even_iff.mp he
    · have h2 : 2 ≤ h := by
        rcases he with ⟨k, hk⟩
        omega
      simp [h2, he]
  · right
    constructor
    · exact Nat.odd_iff.mp (Nat.not_even_iff_odd.mp he)
    · simp [he]
