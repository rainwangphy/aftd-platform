import AFTD.Prelude

/-!
# renyi_entropy

Topic: information   Node: 48fd21e67026

Provenance: formalization of a published result. Source: Renyi 1961, On measures of entropy and information

For a real parameter α and a probability distribution P on a finite type Y, renyi_entropy α P is the Rényi entropy (log(∑_y P(y)^α)) / (1 - α).
-/

/-- Rényi entropy of order α of a discrete probability distribution P on a finite type. -/
noncomputable def renyi_entropy (α : ℝ) {Y : Type*} [Fintype Y] (P : Y → ℝ) : ℝ := Real.log (∑ y, P y ^ α) / (1 - α)
