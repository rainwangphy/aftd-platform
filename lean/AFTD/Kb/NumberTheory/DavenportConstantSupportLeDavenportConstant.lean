import AFTD.Prelude
import AFTD.Kb.NumberTheory.DavenportConstantSupport
import AFTD.Kb.NumberTheory.DavenportConstant
import AFTD.Kb.NumberTheory.MultisetIsMinimalZeroSum

/-!
# davenport_constant_support_le_davenport_constant

Topic: elementary_number_theory   Node: 7cf5cd3edc7f

Provenance: helper lemma. Sanity lemma for davenport_constant_support.

Restricting the support size can only lower the maximal length: D^{(k)}(X) ≤ D(X).
-/

theorem davenport_constant_support_le_davenport_constant {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (k : ℕ) (X : Set G) : davenport_constant_support k X ≤ davenport_constant X := by
  unfold davenport_constant_support davenport_constant
  apply sSup_le_sSup
  rintro n ⟨s, hX, hmin, -, hcard⟩
  exact ⟨s, hX, hmin, hcard⟩
