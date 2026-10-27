import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_only_coloured_cover_counterexample

Topic: combinatorics   Node: ffbe9e874cfe

Provenance: helper lemma. Counterexample to a proposed shortcut in OP-205 / RT-1, following arXiv:2610.15635. The missing ordinary edge is explicit, so this is not a counterexample to the paper or the main full-cover conjecture. Experiment6382; no research advance claimed.

At radius eight and period twenty, four real class colours can coexist with tight classes, constant active count four, exact coverage of all dyadic long edges and disjoint classes of each colour, yet an ordinary distance-one edge is uncovered. Thus keeping the palette does not make dyadic-only coverage force divisibility.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem cycle_power_dyadic_only_coloured_cover_counterexample :
    ∃ (x : ZMod 20 → ℕ → Bool) (ell : ZMod 20 → ℕ),
      (∀ p, ell p < 4) ∧
      (∀ p, x p 0 = true ∧ x p 7 = true) ∧
      (∀ p, cycle_power_dyadic_class_weight 3 (x p) =
        (Finset.range 8).sum (fun a => (x p a).toNat)) ∧
      (∀ v : ZMod 20, (Finset.range 8).sum (fun a =>
        (x (v - (a : ZMod 20)) a).toNat) = 4) ∧
      (∀ (j : Fin 3) (v : ZMod 20),
        (Finset.range (2 ^ (j : ℕ))).sum (fun a =>
          (x (v - (a : ZMod 20)) a &&
            x (v - (a : ZMod 20)) (a + 8 - 2 ^ (j : ℕ))).toNat) = 1) ∧
      (∀ (v : ZMod 20) (a b : Fin 8), a ≠ b →
        x (v - ((a : ℕ) : ZMod 20)) a = true →
        x (v - ((b : ℕ) : ZMod 20)) b = true →
        ell (v - ((a : ℕ) : ZMod 20)) ≠ ell (v - ((b : ℕ) : ZMod 20))) ∧
      (∀ a ∈ Finset.range 7,
        ¬(x ((2 : ZMod 20) - (a : ZMod 20)) a = true ∧
          x ((2 : ZMod 20) - (a : ZMod 20)) (a + 1) = true)) := by
  let x : ZMod 20 → ℕ → Bool := fun p a => decide (a ∈
    match p.val with
    | 0 => ({0, 1, 3, 4, 6, 7} : Finset ℕ)
    | 1 => {0, 1, 5, 7}
    | 2 => {0, 3, 7}
    | 3 => {0, 1, 6, 7}
    | 4 => {0, 4, 7}
    | 5 => {0, 2, 6, 7}
    | 6 => {0, 1, 3, 4, 6, 7}
    | 7 => {0, 1, 5, 7}
    | 8 => {0, 3, 7}
    | 9 => {0, 1, 5, 6, 7}
    | 10 => {0, 7}
    | 11 => {0, 2, 6, 7}
    | 12 => {0, 1, 2, 4, 6, 7}
    | 13 => {0, 7}
    | 14 => {0, 1, 3, 5, 6, 7}
    | 15 => {0, 1, 5, 7}
    | 16 => {0, 7}
    | 17 => {0, 1, 2, 6, 7}
    | 18 => {0, 4, 7}
    | _ => {0, 2, 6, 7})
  let ell : ZMod 20 → ℕ := fun p =>
    match p.val with
    | 0 => 0
    | 1 => 2
    | 2 => 0
    | 3 => 1
    | 4 => 3
    | 5 => 2
    | 6 => 3
    | 7 => 1
    | 8 => 0
    | 9 => 2
    | 10 => 0
    | 11 => 1
    | 12 => 0
    | 13 => 2
    | 14 => 3
    | 15 => 1
    | 16 => 3
    | 17 => 2
    | 18 => 3
    | _ => 1
  refine ⟨x, ell, ?_⟩
  decide
