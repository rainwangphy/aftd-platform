import AFTD.Prelude

/-!
# randomized_littlestone

Topic: learning   Node: 6e28dfa8163b

Provenance: formalization of a published result. Source: arXiv:2611.28727 Lemma 27(a)

The rational-valued randomised Littlestone dimension of a finite concept class H : Finset (α → Bool) on a finite type α with decidable equality, taking values in ℚ, defined recursively: 0 if H.card ≤ 1, and otherwise the maximum over all points x : α that split H (having both fibers nonempty) of (1 + RL(H_x^false) + RL(H_x^true)) / 2 (or 0 if no point splits H).
-/

/-- The rational-valued randomised Littlestone dimension of a finite concept class on a finite domain, via recursive minimax. -/
def randomized_littlestone {α : Type*} [Fintype α] [DecidableEq α] (H : Finset (α → Bool)) : ℚ :=
  let rec fuel : ℕ → Finset (α → Bool) → ℚ
    | 0, _ => 0
    | f + 1, V =>
      if V.card ≤ 1 then 0
      else
        let splits := Finset.univ.filter fun x =>
          (V.filter (· x = false)).Nonempty ∧ (V.filter (· x = true)).Nonempty
        splits.fold max 0 fun x =>
          (1 + fuel f (V.filter (· x = false)) + fuel f (V.filter (· x = true))) / 2
  fuel H.card H
