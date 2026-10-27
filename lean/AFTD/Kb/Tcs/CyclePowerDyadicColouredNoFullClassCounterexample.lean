import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_coloured_no_full_class_counterexample

Topic: combinatorics   Node: 9a9cfb8c57eb

Provenance: helper lemma. Counterexample to the proposed full-interval-class/peeling shortcut in OP-205 / RT-1, experiment6410, following arXiv:2610.15635. The eight-row pattern is pulled back to integers with period448, which is in the original large-size range at bandwidth seven. Since eight divides448, this is not a counterexample to the main conjecture. The theorem is explicitly about the coloured class model; no new research advance claimed.

A period-448 integer radius-eight model with four real class colours has tight classes, constant active count four, every dyadic edge covered exactly once, full ordinary coverage and same-colour disjointness, but every class has size at most six and misses offset four. An optimal-model fullness assumption is therefore false.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem cycle_power_dyadic_coloured_no_full_class_finite :
    ∃ (b : ZMod 8 → ℕ → Bool) (ell : ZMod 8 → ℕ),
      (∀ p, ell p < 4) ∧
      (∀ p, b p 0 = true ∧ b p 7 = true ∧ b p 4 = false) ∧
      (∀ p, cycle_power_dyadic_class_weight 3 (b p) =
        (range 8).sum (fun a => (b p a).toNat)) ∧
      (∀ p, (range 8).sum (fun a => (b p a).toNat) ≤ 6) ∧
      (∀ v : ZMod 8, (range 8).sum (fun a =>
        (b (v - (a : ZMod 8)) a).toNat) = 4) ∧
      (∀ (j : Fin 3) (v : ZMod 8), (range (2 ^ (j : ℕ))).sum (fun a =>
        (b (v - (a : ZMod 8)) a &&
          b (v - (a : ZMod 8)) (a + 8 - 2 ^ (j : ℕ))).toNat) = 1) ∧
      (∀ (d : Fin 7) (v : ZMod 8), ∃ a ∈ range (8 - ((d : ℕ) + 1)),
        b (v - (a : ZMod 8)) a = true ∧
          b (v - (a : ZMod 8)) (a + ((d : ℕ) + 1)) = true) ∧
      (∀ (v : ZMod 8) (a b' : Fin 8), a ≠ b' →
        b (v - ((a : ℕ) : ZMod 8)) a = true →
        b (v - ((b' : ℕ) : ZMod 8)) b' = true →
        ell (v - ((a : ℕ) : ZMod 8)) ≠ ell (v - ((b' : ℕ) : ZMod 8))) := by
  let b : ZMod 8 → ℕ → Bool := fun p a => decide (a ∈
    if p.val % 2 = 0 then ({0, 7} : Finset ℕ) else {0, 1, 2, 3, 6, 7})
  let ell : ZMod 8 → ℕ := fun p =>
    match p.val with
    | 0 => 0
    | 1 => 2
    | 2 => 3
    | 3 => 0
    | 4 => 1
    | 5 => 3
    | 6 => 2
    | _ => 1
  refine ⟨b, ell, ?_⟩
  decide

theorem cycle_power_dyadic_coloured_no_full_class_counterexample :
    ∃ (x : ℤ → ℕ → Bool) (ell : ℤ → ℕ),
      (∀ p a, x (p + 448) a = x p a) ∧
      (∀ p, ell (p + 448) = ell p) ∧
      (∀ p, ell p < 4) ∧
      (∀ p, x p 0 = true ∧ x p 7 = true ∧ x p 4 = false) ∧
      (∀ p, cycle_power_dyadic_class_weight 3 (x p) =
        (range 8).sum (fun a => (x p a).toNat)) ∧
      (∀ p, (range 8).sum (fun a => (x p a).toNat) ≤ 6) ∧
      (∀ v : ℤ, (range 8).sum (fun a => (x (v - (a : ℤ)) a).toNat) = 4) ∧
      (∀ j < 3, ∀ v : ℤ, (range (2 ^ j)).sum (fun a =>
        (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 8 - 2 ^ j)).toNat) = 1) ∧
      (∀ d : ℕ, 1 ≤ d → d < 8 → ∀ v : ℤ,
        ∃ a ∈ range (8 - d), x (v - (a : ℤ)) a = true ∧
          x (v - (a : ℤ)) (a + d) = true) ∧
      (∀ (v : ℤ) (a b : Fin 8), a ≠ b →
        x (v - ((a : ℕ) : ℤ)) a = true → x (v - ((b : ℕ) : ℤ)) b = true →
        ell (v - ((a : ℕ) : ℤ)) ≠ ell (v - ((b : ℕ) : ℤ))) := by
  obtain ⟨b, ell, hbnd, he, hw, hsize, hcount, hexact, hcover, hcol⟩ :=
    cycle_power_dyadic_coloured_no_full_class_finite
  refine ⟨fun p a => b (p : ZMod 8) a, fun p => ell (p : ZMod 8),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p a
    simp only [Int.cast_add, Int.cast_ofNat]
    have hz : (448 : ZMod 8) = 0 := by decide
    rw [hz, add_zero]
  · intro p
    simp only [Int.cast_add, Int.cast_ofNat]
    have hz : (448 : ZMod 8) = 0 := by decide
    rw [hz, add_zero]
  · intro p; exact hbnd (p : ZMod 8)
  · intro p; exact he (p : ZMod 8)
  · intro p; exact hw (p : ZMod 8)
  · intro p; exact hsize (p : ZMod 8)
  · intro v
    simpa only [Int.cast_sub, Int.cast_natCast] using hcount (v : ZMod 8)
  · intro j hj v
    simpa only [Int.cast_sub, Int.cast_natCast] using hexact ⟨j, hj⟩ (v : ZMod 8)
  · intro d hd hd8 v
    have hlt : d - 1 < 7 := by omega
    have heq : d - 1 + 1 = d := by omega
    obtain ⟨a, ha, h1, h2⟩ := hcover ⟨d - 1, hlt⟩ (v : ZMod 8)
    simp only [heq] at ha h1 h2
    exact ⟨a, ha, by simpa only [Int.cast_sub, Int.cast_natCast] using h1,
      by simpa only [Int.cast_sub, Int.cast_natCast] using h2⟩
  · intro v a b' hab ha hb
    simpa only [Int.cast_sub, Int.cast_natCast] using
      hcol (v : ZMod 8) a b' hab
        (by simpa only [Int.cast_sub, Int.cast_natCast] using ha)
        (by simpa only [Int.cast_sub, Int.cast_natCast] using hb)
