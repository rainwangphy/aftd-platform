import AFTD.Prelude

/-!
# iid_word_measure

Topic: algorithms   Node: 6c880c5ec4f6

Provenance: original. Related work: folklore

Given natural numbers q and N, and real weights p : Fin q → ℝ, iid_word_measure q N p is the product measure on words Fin N → Fin q defined by MeasureTheory.Measure.pi where each coordinate has marginal measure ∑ i : Fin q, ENNReal.ofReal (p i) • MeasureTheory.Measure.dirac i.
-/

/-- The product measure on length-N words over alphabet Fin q with independent coordinates distributed according to probability weights p. -/
noncomputable def iid_word_measure (q N : ℕ) (p : Fin q → ℝ) : MeasureTheory.Measure (Fin N → Fin q) := MeasureTheory.Measure.pi (fun _ : Fin N => ∑ i : Fin q, ENNReal.ofReal (p i) • MeasureTheory.Measure.dirac i)
