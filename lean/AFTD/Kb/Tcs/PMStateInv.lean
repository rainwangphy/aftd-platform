import AFTD.Prelude
import AFTD.Kb.Tcs.PmFam
import AFTD.Kb.Tcs.PMSat
import AFTD.Kb.Tcs.PMState

/-!
# PMState.Inv

Topic: algorithms   Node: 3e8e081231b5

The adversary invariant.
-/

/-- The adversary invariant. -/
def PMState.Inv {n : ℕ} (S : PMState n) : Prop :=
  (∀ f ∈ S.facts, S.comp f.1 = S.comp f.2.1) ∧
  PMSat (pmFam S.col S.rk) S.facts ∧
  (∀ f ∈ S.facts, f.1 ∈ S.alive → f.2.1 ∈ S.alive → f.1 ≠ f.2.1 →
      S.col f.1 ≠ S.col f.2.1) ∧
  (∀ x ∈ S.alive, S.rk x = (x.val : ℤ)) ∧
  (∀ x, x ∉ S.alive → (n : ℤ) + S.alive.card ≤ S.rk x) ∧
  Function.Injective S.rk ∧
  (∀ x, ∃ a ∈ S.alive, S.comp a = S.comp x)
