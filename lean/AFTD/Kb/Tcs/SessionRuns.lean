import AFTD.Prelude

/-!
# session_runs

Topic: online_algorithms   Node: 9910405dafcf

Provenance: formalization of a published result. Source: arXiv:2611.06955, Definition 2

Given a horizon T : ℕ and an increment vector a : Fin (T - 1) → NNReal, the number of runs session_runs T a : ℕ is 0 if T ≤ 1, and 1 plus the cardinality of the finset of indices i : Fin (T - 2) such that a ⟨i.val, _⟩ ≠ a ⟨i.val + 1, _⟩ otherwise.
-/

/-- The number of runs of a session of horizon T with increments a. -/
noncomputable def session_runs (T : ℕ) (a : Fin (T - 1) → NNReal) : ℕ := if T ≤ 1 then 0
  else
    1 + ((Finset.univ.filter (fun i : Fin (T - 2) =>
      a ⟨i.val, by omega⟩ ≠ a ⟨i.val + 1, by omega⟩)).card)
