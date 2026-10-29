import AFTD.Prelude

/-!
# cycle_power_rooted_reflect

Topic: combinatorics   Node: 927b7415827f

Provenance: helper lemma. Uniform structural route for OP-205 / RT-1, following arXiv:2610.15635. These are helper reductions, not a proof of the open covering value and not a research advance. The upper-vertical core remains an explicit unproved hypothesis.

Reflects the offsets of a rooted Boolean profile in its arc of length D and changes its integer root so that physical lattice points are negated.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def cycle_power_rooted_reflect (D : ℕ) (x : ℤ → ℕ → Bool) : ℤ → ℕ → Bool :=
  fun p a => x (-p-((D-1 : ℕ) : ℤ)) (D-1-a)
