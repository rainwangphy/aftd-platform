import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicFullGapClassNoIsland
import AFTD.Kb.Tcs.IntDenseMarksBracket
import AFTD.Kb.Tcs.CyclePowerTwoFullRootsHalfSeparated

/-!
# cycle_power_dyadic_class_no_island_of_full_class_cover

Topic: combinatorics   Node: b2341f051e15

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

A positive-exponent integer dyadic rooted-class model with tight weights, exact dyadic pair ownership, all ordinary distance coverage, and a full class covering every vertex has no selected island between two missing offsets in any class.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_class_no_island_of_full_class_cover
    (m : ℕ) (hm : 1 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p : ℤ, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun i => (x p i).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true)
    (hfullcover : ∀ v : ℤ, ∃ a : ℕ, a < 2^m ∧ ∀ i < 2^m, x (v-(a : ℤ)) i = true) :
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
      x p a = false → x p b = true → x p c = true := by
  classical
  intro p a b c hab hbc hcD hxa hxb
  have hp : ¬(∀ i < 2^m, x p i = true) := by
    intro h
    have := h a (by omega)
    rw [hxa] at this
    contradiction
  obtain ⟨l, r, hl₀, hr₀, hlr, hFl, hFr⟩ := int_dense_marks_bracket
    (2^m) (fun q => ∀ i < 2^m, x q i = true) hfullcover p hp
  let y : ℤ → ℕ → Bool := fun q i => x ((p-(l : ℤ))+q) i
  have hyroot : ∀ i, y (l : ℤ) i = x p i := by intro i; dsimp [y]; congr 1; omega
  have hytight : ∀ q : ℤ, cycle_power_dyadic_class_weight m (y q) =
      (range (2^m)).sum (fun i => (y q i).toNat) := by
    intro q
    exact htight ((p-(l : ℤ))+q)
  have hyexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1 := by
    intro j hj v
    simpa only [y, add_sub_assoc] using hexact j hj ((p-(l : ℤ))+v)
  have hycover : ∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ y (v-(a : ℤ)) a = true ∧ y (v-(a : ℤ)) (a+d) = true := by
    intro d hd₀ hdD v
    simpa only [y, add_sub_assoc] using hcover d hd₀ hdD ((p-(l : ℤ))+v)
  have hyfull₀ : ∀ i < 2^m, y 0 i = true := by
    intro i hi
    simpa only [y, add_zero] using hFl i hi
  have hyfullg : ∀ i < 2^m, y ((l+r : ℕ) : ℤ) i = true := by
    intro i hi
    have hroot : (p-(l : ℤ))+((l+r : ℕ) : ℤ) = p+(r : ℤ) := by omega
    simpa only [y, hroot] using hFr i hi
  have hD : 2^m = 2*2^(m-1) := by
    have he : m = (m-1)+1 := by omega
    conv_lhs => rw [he, pow_succ]
    ring
  have hlo := cycle_power_two_full_roots_half_separated (2^m) (2^(m-1)) hD y
    (hyexact (m-1) (by omega)) (l+r) (by omega) hyfull₀ hyfullg
  have hshape := cycle_power_dyadic_full_gap_class_no_island m hm y hytight hyexact hycover
    (l+r) hlo hlr hyfull₀ hyfullg l hl₀ (by omega) a b c hab hbc hcD
      (by simpa only [hyroot] using hxa) (by simpa only [hyroot] using hxb)
  simpa only [hyroot] using hshape
