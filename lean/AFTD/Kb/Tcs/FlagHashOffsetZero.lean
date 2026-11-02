import AFTD.Prelude
import AFTD.Kb.Tcs.GroupPrimeCompositionSeries
import AFTD.Kb.Tcs.FlagRepresentatives
import AFTD.Kb.Tcs.FlagHashOffset

/-!
# flag_hash_offset_zero

Topic: data_structures   Node: 02fadda2b1b0

Provenance: helper lemma. arXiv:2610.31363: A Sharp Analysis of Fixed Offset Hash Tables, serving OP-808

For any group G, natural number k, prime quotient orders p : Fin k → ℕ, prime composition series series : GroupPrimeCompositionSeries G k p, and flag representatives reps : FlagRepresentatives series, the offset flag_hash_offset reps ⟨0, Finset.prod_pos fun i _ => (series.prime i).pos⟩ is equal to 1.
-/

/-- The 0-th offset in a solvable group flag hash sequence is the group identity. -/
theorem flag_hash_offset_zero {G : Type*} [Group G] {k : ℕ} {p : Fin k → ℕ}
    {series : GroupPrimeCompositionSeries G k p} (reps : FlagRepresentatives series) :
    flag_hash_offset reps ⟨0, Finset.prod_pos fun i _ => (series.prime i).pos⟩ = 1 := by
  simp [flag_hash_offset, reps.zero]
