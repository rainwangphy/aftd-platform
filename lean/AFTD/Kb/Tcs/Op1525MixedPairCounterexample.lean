import AFTD.Prelude

/-!
# op1525_mixed_pair_counterexample

Topic: combinatorics   Node: 82ff5ee53425

Provenance: helper lemma. A finite obstruction for OP-1525, found by recorded permutation-action computation 24925; this is not a signed-graph counterexample.

There is an eight-point permutation action with two fixed points and an invariant two-point orbit, and two nonequivalent colorings whose one-point switch decks agree. The two-point orbit has different colors, showing why the monochromatic-pair hypothesis cannot simply be dropped in the abstract criterion.
-/

theorem op1525_mixed_pair_counterexample :
    let V := Fin 2 ⊕ (Fin 2 ⊕ Fin 4)
    let a : V → Bool := fun x => match x with
      | .inl _ => false
      | .inr (.inl i) => decide (i = 0)
      | .inr (.inr i) => decide (i = 0 ∨ i = 3)
    let b : V → Bool := fun x => match x with
      | .inl _ => false
      | .inr (.inl i) => decide (i = 1)
      | .inr (.inr i) => decide (i = 0 ∨ i = 3)
    let rot : Fin 4 → V → V := fun k x => match x with
      | .inl i => .inl i
      | .inr (.inl i) => .inr (.inl (i + if k = 0 ∨ k = 2 then 0 else 1))
      | .inr (.inr i) => .inr (.inr (i + k))
    let flip : (V → Bool) → V → V → Bool :=
      fun f v i => xor (f i) (decide (i = v))
    let equiv : (V → Bool) → (V → Bool) → Prop :=
      fun f g => ∃ (k : Fin 4) (c : Bool), ∀ i : V, f (rot k i) = xor (g i) c
    ¬ equiv a b ∧ ∃ p : Equiv.Perm V, ∀ v, equiv (flip a v) (flip b (p v)) := by
  dsimp only
  constructor
  · decide
  · refine ⟨(Equiv.swap (.inl 0) (.inl 1)).trans
      ((Equiv.swap (.inr (.inl 0)) (.inr (.inl 1))).trans
        ((Equiv.swap (.inr (.inr 0)) (.inr (.inr 3))).trans
          (Equiv.swap (.inr (.inr 1)) (.inr (.inr 2))))), ?_⟩
    decide
