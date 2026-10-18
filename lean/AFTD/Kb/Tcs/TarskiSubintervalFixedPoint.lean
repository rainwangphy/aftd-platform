import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# tarski_subinterval_fixed_point

Topic: algorithms   Node: f5e7483f758e

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Subinterval fixed point theorem: if a monotone map f satisfies a ≤ f(a) and f(b) ≤ b, then f has a fixed point in the sub-box [a, b].
-/

/-- Subinterval fixed point theorem: if a monotone map f satisfies a ≤ f(a) and f(b) ≤ b, then f has a fixed point in the sub-box [a, b]. -/
theorem tarski_subinterval_fixed_point (n k : ℕ) [NeZero n]
    (f : (Fin k → Fin n) → (Fin k → Fin n)) (hf : Monotone f)
    (a b : Fin k → Fin n) (hab : a ≤ b) (ha : a ≤ f a) (hb : f b ≤ b) :
    ∃ x : Fin k → Fin n, a ≤ x ∧ x ≤ b ∧ f x = x := by
  let F : (Fin k → Fin n) →o (Fin k → Fin n) := ⟨f, hf⟩
  have ha' : a ≤ F a := ha
  let x : Fin k → Fin n := (F.nextFixed a ha' : (Fin k → Fin n))
  have hxfix : f x = x := (F.nextFixed a ha').2
  have hax : a ≤ x := F.le_nextFixed ha'
  have hxb : x ≤ b := by
    change (OrderHom.const (Fin k → Fin n) a ⊔ F).lfp ≤ b
    apply OrderHom.lfp_le
    change a ⊔ f b ≤ b
    exact sup_le hab hb
  exact ⟨x, hax, hxb, hxfix⟩
