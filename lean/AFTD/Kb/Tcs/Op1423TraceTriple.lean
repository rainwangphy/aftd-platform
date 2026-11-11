import AFTD.Prelude
import AFTD.Kb.Tcs.NumericalSemigroup

/-!
# op_1423_trace_triple

Topic: combinatorics   Node: 5a240e266b0d

Provenance: helper lemma. step towards op_1423_two_band_binomial_count

The band trace triple of a numerical semigroup S for the parameters F and m: its intersections with [m,2m), [2m,3m) and [3m,F), as three finite sets.
-/

/-- The trace of a numerical semigroup on the three bands [m,2m), [2m,3m) and [3m,F). -/
noncomputable def op_1423_trace_triple (F m : ℕ) (S : NumericalSemigroup) : (Finset ℕ × Finset ℕ) × Finset ℕ := by
  classical
  exact ⟨⟨(Finset.Ico m (2*m)).filter (fun n => n ∈ (S.toAddSubmonoid : Set ℕ)),
      (Finset.Ico (2*m) (3*m)).filter (fun n => n ∈ (S.toAddSubmonoid : Set ℕ))⟩,
      (Finset.Ico (3*m) F).filter (fun n => n ∈ (S.toAddSubmonoid : Set ℕ))⟩
