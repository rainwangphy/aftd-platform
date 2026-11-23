import AFTD.Prelude

/-!
# ballBearingRingSet

Topic: integer_programming   Node: 7ab3be5e9efe

Provenance: helper lemma. step towards ball_bearing_tsp_sec_lower_bound

For a natural number k and a subset B' of Fin k, the vertex set S(B') of Fin k × Fin 5 consisting of all inner vertices (j,0) together with the ball vertices (j,1) for j ∈ B'. These are the 'cheap' vertex sets I ⊆ S ⊆ I ∪ B of the Ball Bearing construction.
-/

/-- The cheap vertex set S(B'): all inner vertices, plus the balls indexed by B'. -/
def ballBearingRingSet (k : ℕ) (B' : Finset (Fin k)) : Finset (Fin k × Fin 5) := Finset.univ.filter (fun p => p.2 = (0 : Fin 5) ∨ (p.2 = 1 ∧ p.1 ∈ B'))
