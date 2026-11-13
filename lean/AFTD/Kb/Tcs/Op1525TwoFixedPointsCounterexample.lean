import AFTD.Prelude
import AFTD.Kb.Tcs.Op1525ThreeFixedPointsReconstruct

/-!
# op1525_two_fixed_points_counterexample

Topic: combinatorics   Node: 34fa468c46fa

Provenance: helper lemma. Boundary example for op1525_three_fixed_points_reconstruct and OP-1525; compare arXiv:2611.13901, Section 4.1.

On the disjoint union of two fixed points and a six-point cyclic orbit, the indicated two colorings are not equivalent under a rotation and a global color exchange, but their one-point switch decks can be matched by a bijection under that equivalence. Thus the three-fixed-point reconstruction criterion cannot be weakened to two fixed points for arbitrary permutation actions.
-/

theorem op1525_two_fixed_points_counterexample :
    let V := Fin 2 ⊕ Fin 6
    let a : V → Bool := fun x => match x with
      | .inl i => decide (i = 0)
      | .inr i => decide (i = 0 ∨ i = 1 ∨ i = 3)
    let b : V → Bool := fun x => match x with
      | .inl i => decide (i = 1)
      | .inr i => decide (i = 0 ∨ i = 1 ∨ i = 3)
    let rot : Fin 6 → V → V := fun k x => match x with
      | .inl i => .inl i
      | .inr i => .inr (i + k)
    let flip : (V → Bool) → V → V → Bool :=
      fun f v i => xor (f i) (decide (i = v))
    let equiv : (V → Bool) → (V → Bool) → Prop :=
      fun f g => ∃ (k : Fin 6) (c : Bool), ∀ i : V, f (rot k i) = xor (g i) c
    ¬ equiv a b ∧ ∃ p : Equiv.Perm V, ∀ v, equiv (flip a v) (flip b (p v)) := by
  dsimp only
  constructor
  · decide
  · refine ⟨(Equiv.swap (.inl 0) (.inl 1)).trans
      ((Equiv.swap (.inr 0) (.inr 5)).trans
        ((Equiv.swap (.inr 1) (.inr 4)).trans (Equiv.swap (.inr 2) (.inr 3)))), ?_⟩
    decide
