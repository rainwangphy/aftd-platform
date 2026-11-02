import AFTD.Prelude

/-!
# ising_ring_spin

Topic: statistical_mechanics   Node: 2c9b435644ca

Provenance: helper lemma. arXiv:2610.39815, Sections 2–4; helper for OP-806.

Maps a Boolean spin to the real value +1 for true and -1 for false.
-/

noncomputable def ising_ring_spin (b : Bool) : ℝ := if b then 1 else -1
