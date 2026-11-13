import AFTD.Prelude

/-!
# signed_graph_cyclic_eight_switch_deck_obstruction

Topic: combinatorics   Node: 0b211cbd11be

Provenance: helper lemma. OP-1525, arXiv:2611.13901; obstruction to proving reconstruction for arbitrary permutation groups acting on the balance partition.

On the cyclic group of order eight, take subsets {0,1,3} and {0,2,3}. No rotation or global complement carries one to the other, but there is a bijection of the eight vertices matching their one-vertex switch cards up to rotation and global complement. This is a permutation-group obstruction, not a counterexample for undirected graphs.
-/

theorem signed_graph_cyclic_eight_switch_deck_obstruction :
    let a : Fin 8 → Bool := fun i => decide (i = 0 ∨ i = 1 ∨ i = 3)
    let b : Fin 8 → Bool := fun i => decide (i = 0 ∨ i = 2 ∨ i = 3)
    let flip : (Fin 8 → Bool) → Fin 8 → Fin 8 → Bool :=
      fun f v i => xor (f i) (decide (i = v))
    let equiv : (Fin 8 → Bool) → (Fin 8 → Bool) → Prop :=
      fun f g => ∃ (k : Fin 8) (c : Bool), ∀ i : Fin 8, f (i + k) = xor (g i) c
    ¬ equiv a b ∧ ∃ p : Equiv.Perm (Fin 8), ∀ v, equiv (flip a v) (flip b (p v)) := by
  dsimp only
  constructor
  · decide
  · refine ⟨(Equiv.swap 0 3).trans ((Equiv.swap 1 2).trans ((Equiv.swap 4 7).trans (Equiv.swap 5 6))), ?_⟩
    decide
