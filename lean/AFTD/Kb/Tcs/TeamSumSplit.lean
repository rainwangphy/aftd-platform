import AFTD.Prelude

/-!
# team_sum_split

Topic: algorithms   Node: ea1f23e54f6d

Splitting a sum over outcome vectors of length n+1 by the first outcome.
-/

open Finset in
/-- Splitting a sum over outcome vectors of length `n+1` by the first outcome. -/
lemma team_sum_split {n : ℕ} (F : (Fin (n + 1) → Bool) → ℝ) :
    ∑ ω, F ω = ∑ ω : Fin n → Bool, (F (Fin.cons true ω) + F (Fin.cons false ω)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool, ← Finset.sum_add_distrib]
  rfl
