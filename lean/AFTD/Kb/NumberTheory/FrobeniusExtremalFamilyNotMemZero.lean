import AFTD.Prelude
import AFTD.Kb.NumberTheory.FrobeniusExtremalFamily

/-!
# frobenius_extremal_family_not_mem_zero

Topic: elementary_number_theory   Node: a3249924f86a

Provenance: helper lemma. scout/2610-32219-a-sharp-upper-bound-for-the-frobenius-number.md:454

If q ≥ 1, then 0 does not belong to `frobenius_extremal_family n q`.
-/

/-- Zero does not belong to the extremal family S_{n,q} when q ≥ 1. -/
theorem frobenius_extremal_family_not_mem_zero (n q : ℕ) (hq : 1 ≤ q) : 0 ∉ frobenius_extremal_family n q := by
  intro h
  simp only [frobenius_extremal_family, Set.mem_union, Set.mem_singleton_iff] at h
  rcases h with ⟨i, hi1, -, hi0⟩ | h0
  · have : i * q ≠ 0 := mul_ne_zero (by omega) (by omega)
    exact this hi0.symm
  · omega
