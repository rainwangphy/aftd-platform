import AFTD.Prelude

/-!
# rent_or_buy_num_runs

Topic: online_algorithms   Node: 8a3400205fba

Provenance: formalization of a published result. Source: arXiv:2611.06955 Definition 2

Given a horizon T : ℕ and increments a : Fin (T - 1) → NNReal, rent_or_buy_num_runs T a : ℕ is defined as: if 2 ≤ T, 1 plus the cardinality of the finset of indices i : Fin (T - 2) such that a ⟨i.val + 1, _⟩ ≠ a ⟨i.val, _⟩; and 0 otherwise.
-/

/-- The number of runs of a session with horizon T and increments a : Fin (T - 1) → NNReal. -/
noncomputable def rent_or_buy_num_runs (T : ℕ) (a : Fin (T - 1) → NNReal) : ℕ := if hT : 2 ≤ T then
    1 + ((Finset.univ : Finset (Fin (T - 2))).filter
      (fun i => a ⟨i.val + 1, by omega⟩ ≠ a ⟨i.val, by omega⟩)).card
  else
    0
