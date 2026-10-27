import AFTD.Prelude
import AFTD.Kb.NumberTheory.FrobeniusExtremalFamily

/-!
# frobenius_extremal_family_mem_generator

Topic: elementary_number_theory   Node: b457ec72093e

Provenance: helper lemma. scout/2610-32219-a-sharp-upper-bound-for-the-frobenius-number.md:454

If n ≥ 2, then q belongs to the extremal set family `frobenius_extremal_family n q`.
-/

/-- The generator q belongs to the extremal family S_{n,q} when n ≥ 2. -/
theorem frobenius_extremal_family_mem_generator (n q : ℕ) (hn : 2 ≤ n) : q ∈ frobenius_extremal_family n q := by
  unfold frobenius_extremal_family
  left
  exact ⟨1, le_refl 1, by omega, by simp⟩
