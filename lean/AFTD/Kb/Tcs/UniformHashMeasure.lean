import AFTD.Prelude

/-!
# uniform_hash_measure

Topic: online_algorithms   Node: 78ab72516681

Provenance: formalization of a published result. Source: arXiv:2610.15776

The uniform probability measure on sequences of n independent uniform home slots in ZMod n.
-/

/-- Uniform probability measure on hash table home slot sequences of length n. -/
noncomputable def uniform_hash_measure (n : ℕ) [NeZero n] : MeasureTheory.Measure (Fin n → ZMod n) :=
  ((n : ENNReal) ^ n)⁻¹ • (MeasureTheory.Measure.count : MeasureTheory.Measure (Fin n → ZMod n))
