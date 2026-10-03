import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TfjrBallot

/-!
# tfjr_count

Topic: social_choice   Node: 44e59b8d5c00

In the counterexample, every nonempty group either contains voter 2 or 3, or has a member who approves nothing in at least ⌈(|T|+1)|S|/4⌉ - 1 rounds of T (checked by decide).
-/

/-- For groups inside `{0, 1}`, some member approves nothing on enough rounds of `T`. -/
theorem tfjr_count : ∀ S : Finset (Fin 4), ∀ T : Finset (Fin 6), S.Nonempty →
    (∃ i ∈ S, 2 ≤ i.val) ∨
      ∃ j ∈ S, ((T.card + 1) * S.card + 4 - 1) / 4 - 1 ≤
        (T.filter fun r => tfjr_ballot j r = ∅).card := by
  decide
