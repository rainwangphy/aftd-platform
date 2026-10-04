import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceEntropy
import AFTD.Kb.GameTheoryEconomics.PlackettLuceEntropyGeometricLe

/-!
# plackett_luce_geometric_entropy_linear

Topic: social_choice   Node: e4fde462764a

Conjecture of Preference Elicitation as Average-Case Sorting (AAAI 2021): for every phi in (0,1) the Plackett-Luce model with weights (1, phi, ..., phi^(m-1)) has entropy O(m).
-/

/-- **Conjecture of Preference Elicitation as Average-Case Sorting (AAAI 2021, after Thm 12).** For every `φ ∈ (0,1)`, the Plackett–Luce model with weights `(1, φ, …, φ^(m-1))` has entropy `O(m)`. -/
theorem plackett_luce_geometric_entropy_linear (φ : ℝ) (h0 : 0 < φ) (h1 : φ < 1) :
    ∃ C : ℝ, ∀ m : ℕ, plackett_luce_entropy (fun i => φ ^ i) (Finset.range m) ≤ C * m :=
  ⟨_, fun m => by
    simpa using plackett_luce_entropy_geometric_le φ h0 h1 m (Finset.range m) (Finset.card_range m)⟩
