import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# tarski_fixed_point_exists

Topic: algorithms   Node: 124449bf5e98

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Every monotone self-map on the discrete grid [n]^k possesses at least one fixed point, by Tarski's fixed point theorem on finite complete lattices.
-/

/-- Every monotone self-map on the discrete grid [n]^k has a fixed point, by Tarski's fixed point theorem on finite complete lattices. -/
theorem tarski_fixed_point_exists (n k : ℕ) (hn : 1 ≤ n)
    (f : (Fin k → Fin n) → (Fin k → Fin n)) (hf : Monotone f) :
    ∃ x : Fin k → Fin n, f x = x := by
  have : NeZero n := ⟨by omega⟩
  let F : (Fin k → Fin n) →o (Fin k → Fin n) := ⟨f, hf⟩
  exact ⟨OrderHom.lfp F, F.map_lfp⟩
