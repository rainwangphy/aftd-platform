import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEf1Fair
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_eef1_fair

Topic: fair_division   Node: 944d2fdc2af3

An allocation is epistemic-EF1-fair to agent i if some allocation gives i the same bundle and is EF1-fair to her.
-/

/-- Epistemic EF1 (Garg-Sharma Def. 9 with F = EF1): some allocation `τ` gives agent `i` the same bundle as `σ` and is EF1-fair to her. -/
def is_eef1_fair {m n : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (σ : Fin m → Fin n) (i : Fin n) : Prop :=
  ∃ τ : Fin m → Fin n, bundle_of τ i = bundle_of σ i ∧ is_ef1_fair v τ i
