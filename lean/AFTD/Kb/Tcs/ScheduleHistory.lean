import AFTD.Prelude

/-!
# schedule_history

Topic: online_algorithms   Node: 937be31aadcf

Provenance: formalization of a published result. Source: arXiv:2611.06955, Definition 3

Given a horizon T : ℕ, increments a : Fin (T - 1) → NNReal, and a schedule r : Fin T → Bool, schedule_history T a r : Fin T → NNReal is defined recursively: at index ⟨0, _⟩ it is 0, and at index ⟨t + 1, _⟩ it is a ⟨t, _⟩ if r ⟨t, _⟩ is true, and schedule_history T a r ⟨t, _⟩ + a ⟨t, _⟩ if r ⟨t, _⟩ is false.
-/

/-- The history of a schedule r on a session of horizon T with increments a at each call. -/
def schedule_history (T : ℕ) (a : Fin (T - 1) → NNReal) (r : Fin T → Bool) : Fin T → NNReal
  | ⟨0, _⟩ => 0
  | ⟨t + 1, ht⟩ =>
    have ht_lt : t < T - 1 := by omega
    if r ⟨t, by omega⟩ then a ⟨t, ht_lt⟩
    else schedule_history T a r ⟨t, by omega⟩ + a ⟨t, ht_lt⟩
termination_by t => t.val
