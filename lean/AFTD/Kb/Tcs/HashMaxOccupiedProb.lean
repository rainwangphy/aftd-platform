import AFTD.Prelude
import AFTD.Kb.Tcs.HashCountFullyOccupied

/-!
# hash_max_occupied_prob

Topic: data_structures   Node: d745cf425d97

Provenance: formalization of a published result. Source: arXiv:2610.31363 Definition 3.2

The maximum probability p_k(t) defined as the supremum of hash_count_fully_occupied n r S t over all S : Finset (ZMod n) with S.card = k, cast to ℝ and divided by (n : ℝ)^t.
-/

/-- The maximum probability p_k(t) that a random length-t sequence fully occupies a target set of k slots. -/
noncomputable def hash_max_occupied_prob (n : ℕ) [NeZero n] (r : Fin n → ZMod n) (k t : ℕ) : ℝ :=
  ((Finset.sup ((Finset.univ : Finset (Finset (ZMod n))).filter (fun S => S.card = k))
    (fun S => hash_count_fully_occupied n r S t) : ℕ) : ℝ) / (n : ℝ) ^ t
