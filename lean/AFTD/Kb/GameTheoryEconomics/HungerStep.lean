import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HungerFiringState

/-!
# hunger_step

Topic: combinatorial_games   Node: b64f26bccd90

Provenance: formalization of a published result. Source: arXiv:2610.08949 Eq (2.1)

For n : ℕ with [NeZero n], a type K with a linear order, additive group structure, and one, a matrix P : Matrix (Fin n) (Fin n) K, and a vector h : Fin n → K, hunger_step P h is the vector sending each j : Fin n to h j + P (hunger_firing_state h) j - (if j = hunger_firing_state h then 1 else 0).
-/

/-- One step of the hunger game dynamics given a transition matrix P. -/
def hunger_step {n : ℕ} [NeZero n] {K : Type*} [LinearOrder K] [AddGroup K] [One K] (P : Matrix (Fin n) (Fin n) K) (h : Fin n → K) : Fin n → K := let i := hunger_firing_state h; fun j => h j + P i j - (if j = i then 1 else 0)
