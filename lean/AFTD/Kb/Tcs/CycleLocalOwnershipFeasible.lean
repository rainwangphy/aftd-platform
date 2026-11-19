import AFTD.Prelude
import AFTD.Kb.Tcs.CycleFactorHighColor
import AFTD.Kb.Tcs.CycleMatchingLowColor
import AFTD.Kb.Tcs.CycleMatchingMissingLowColor

/-!
# cycle_local_ownership_feasible

Topic: graphs   Node: 9f1075ed4afc

Provenance: helper lemma. Local cycle/chord ownership construction for the OP-874 campaign.

A factor cycle has a compatible two-versus-four local coloring with specified matching-port ownership, including all internal matching chords; external matching interfaces are not constrained.
-/

def cycle_local_ownership_feasible
    (n : ℕ) [NeZero n] (b : Fin n → Bool)
    (chord : Fin n → Option (Fin n)) (own : Fin n → Bool) : Prop := ∃ edge : Fin n → Fin 4, ∃ h : Fin n → Fin 3 → Fin 6,
    (∀ i, edge (i-1) ≠ edge i) ∧
    (∀ i, Function.Injective (h i)) ∧
    (∀ i p, h i p ≠ cycle_matching_low_color (b i) ∧
      h i p ≠ cycle_factor_high_color (edge (i-1)) ∧
      h i p ≠ cycle_factor_high_color (edge i)) ∧
    (∀ i, (h i 2 = cycle_matching_missing_low_color (b i)) ↔ own i = true) ∧
    (∀ i, h i 0 ≠ h (i+1) 1 ∧ h i 0 ≠ h (i+1) 2 ∧
      h i 2 ≠ h (i+1) 1 ∧ h i 2 ≠ h (i+1) 2) ∧
    (∀ i j, chord i = some j → b i = b j ∧ own i ≠ own j ∧
      h i 0 ≠ h j 0 ∧ h i 0 ≠ h j 1 ∧
      h i 1 ≠ h j 0 ∧ h i 1 ≠ h j 1)
