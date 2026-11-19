import AFTD.Prelude

/-!
# op309_k5_chord_cycle_spacing_obstruction

Topic: graphs   Node: 0b2e7dfc1cf5

Provenance: helper lemma. Finite obstruction to extending the chord-conflict construction of https://arxiv.org/abs/2611.24297 beyond outerplanar graphs; experiments 34597 and 34600.

In the displayed cyclic ordering of five chord labels, each label appears twice, adjacent labels are distinct, every pair of labels is adjacent somewhere, and every two-coloring makes two monochromatic cycle adjacencies at distance two. This is a finite obstruction to the chord-spacing condition for the displayed Hamiltonian cycle.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem op309_k5_chord_cycle_spacing_obstruction :
  let chord : Fin 10 → Fin 5 := ![0,1,2,0,3,1,4,2,3,4]
  (∀ i : Fin 10, chord i ≠ chord (i+1)) ∧
  (∀ a : Fin 5, (Finset.univ.filter (fun i : Fin 10 => chord i = a)).card = 2) ∧
  (∀ a b : Fin 5, a ≠ b → ∃ i : Fin 10,
    (chord i = a ∧ chord (i+1) = b) ∨ (chord i = b ∧ chord (i+1) = a)) ∧
  (∀ c : Fin 5 → Bool, ∃ i : Fin 10,
    c (chord i) = c (chord (i+1)) ∧ c (chord (i+2)) = c (chord (i+3))) := by
  decide
