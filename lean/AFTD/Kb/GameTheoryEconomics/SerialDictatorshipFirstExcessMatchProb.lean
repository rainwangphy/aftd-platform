import AFTD.Prelude

/-!
# serial_dictatorship_first_excess_match_prob

Topic: matching_markets   Node: c83b1eb76a46

Provenance: formalization of a published result. Source: arXiv:2506.06217, Section 2.1 (Longer Lists Yield Better Matchings)

The real-valued match probability p_n(d) in ℝ of student n+1 in serial dictatorship with n unit-capacity schools and preference lists of length d drawn without replacement, defined by the occupancy birth chain. It returns a real number in ℝ computed as the sum over k ∈ Finset.range (n + 1) of dist n k * (1 - (Nat.choose k d : ℝ) / (Nat.choose n d : ℝ)), where dist 0 k = if k = 0 then 1 else 0, and dist (m + 1) k = dist m k * ((Nat.choose k d : ℝ) / (Nat.choose n d : ℝ)) + (if k = 0 then 0 else dist m (k - 1) * (1 - (Nat.choose (k - 1) d : ℝ) / (Nat.choose n d : ℝ))), where division by zero when Nat.choose n d = 0 evaluates to 0 in ℝ.
-/

/-- Match probability p_n(d) of student n+1 in serial dictatorship, computed via the occupancy birth chain. -/
noncomputable def serial_dictatorship_first_excess_match_prob (n d : ℕ) : ℝ := let rec dist : ℕ → ℕ → ℝ
    | 0 => fun k => if k = 0 then 1 else 0
    | m + 1 => fun k =>
      dist m k * ((Nat.choose k d : ℝ) / (Nat.choose n d : ℝ)) +
        if k = 0 then 0
        else dist m (k - 1) * (1 - (Nat.choose (k - 1) d : ℝ) / (Nat.choose n d : ℝ))
  ∑ k ∈ Finset.range (n + 1),
    dist n k * (1 - (Nat.choose k d : ℝ) / (Nat.choose n d : ℝ))
