import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryComplexityDimLeSucc
import AFTD.Kb.Tcs.TarskiQueryComplexityLe

/-!
# tarski_query_complexity_dim_le

Topic: algorithms   Node: 75fe0c4b3462

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

General dimension simulation reduction: any query algorithm finding a fixed point in dimension k in at most q queries can be simulated in any lower dimension j ≤ k with at most q queries.
-/

/-- Any query algorithm finding a fixed point in dimension k in at most q queries can be simulated in any dimension j ≤ k with at most q queries. -/
theorem tarski_query_complexity_dim_le (n j k q : ℕ) (hjk : j ≤ k) (h : tarski_query_complexity_le n k q) :
    tarski_query_complexity_le n j q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  induction d with
  | zero => simpa using h
  | succ d ih =>
      have h' : tarski_query_complexity_le n (j + d + 1) q := by
        simpa [Nat.add_assoc] using h
      have h'' : tarski_query_complexity_le n (j + d) q :=
        tarski_query_complexity_dim_le_succ n (j + d) q h'
      exact ih (Nat.le_add_right j d) h''
