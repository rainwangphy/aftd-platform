import AFTD.Prelude

/-!
# op1525_even_deletion_switch_counterexample

Topic: combinatorics   Node: 2de3618702bb

Provenance: helper lemma. A finite parity-boundary example for OP-1525, found by recorded computation 25013.

For the cyclic action on six points, the subsets {0,1} and {0,2} have matching ordinary deletion decks, but the card formed by flipping point 4 in the second subset has no match in the first subset’s weak switching deck, even allowing global complementation. Thus odd subset size cannot be removed from the proposed unequal-deck equivalence.
-/

theorem op1525_even_deletion_switch_counterexample :
    let a : Fin 6 → Bool := fun x => decide (x = 0 ∨ x = 1)
    let b : Fin 6 → Bool := fun x => decide (x = 0 ∨ x = 2)
    let erase : (Fin 6 → Bool) → Fin 6 → Fin 6 → Bool :=
      fun f v x => f x && !(decide (x = v))
    let flip : (Fin 6 → Bool) → Fin 6 → Fin 6 → Bool :=
      fun f v x => xor (f x) (decide (x = v))
    let rotateEquiv : (Fin 6 → Bool) → (Fin 6 → Bool) → Prop :=
      fun f g => ∃ k : Fin 6, ∀ x, f (x + k) = g x
    let weakEquiv : (Fin 6 → Bool) → (Fin 6 → Bool) → Prop :=
      fun f g => ∃ (k : Fin 6) (d : Bool), ∀ x, f (x + k) = xor (g x) d
    (∃ π : Equiv.Perm (Fin 6), ∀ v, a v = true →
      rotateEquiv (erase a v) (erase b (π v))) ∧
    ∀ w : Fin 6, ¬ weakEquiv (flip b 4) (flip a w) := by
  dsimp only
  refine ⟨⟨Equiv.swap 1 2, ?_⟩, ?_⟩
  · decide
  · decide
