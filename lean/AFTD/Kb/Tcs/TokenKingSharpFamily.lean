import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicDist

/-!
# token_king_sharp_family

Topic: graphs   Node: 5b433a97dffc

Provenance: formalization of a published result. Source: arXiv:2611.22830

For n : ℕ, token_king_sharp_family n is the finset of elements e in { s : Finset (Fin n) // s.card = 2 } for which there exist u, v : Fin n such that e.val = {u, v} and either cyclic_dist n u v = n / 2 or (cyclic_dist n u v ≤ n / 2 - 3 ∧ cyclic_dist n u v % 2 = 1).
-/

open Classical in
/-- The candidate sharp deficit family of two tokens: all antipodal pairs and all pairs at odd cycle distance at most n/2 - 3. -/
noncomputable def token_king_sharp_family (n : ℕ) : Finset { s : Finset (Fin n) // s.card = 2 } := Finset.univ.filter fun e =>
    ∃ u v : Fin n, e.val = {u, v} ∧
      (cyclic_dist n u v = n / 2 ∨ (cyclic_dist n u v ≤ n / 2 - 3 ∧ cyclic_dist n u v % 2 = 1))
