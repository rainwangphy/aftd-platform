import AFTD.Prelude

/-!
# shannon_entropy

Topic: information   Node: cb5fda564ff6

Provenance: formalization of a published result. Source: Cover and Thomas, Elements of Information Theory

shannon_entropy P is the Shannon entropy of a discrete distribution P on a finite type Y, defined as ∑_y Real.negMulLog (P y).
-/

/-- Shannon entropy of a discrete probability distribution P on a finite type. -/
noncomputable def shannon_entropy {Y : Type*} [Fintype Y] (P : Y → ℝ) : ℝ := ∑ y, Real.negMulLog (P y)
