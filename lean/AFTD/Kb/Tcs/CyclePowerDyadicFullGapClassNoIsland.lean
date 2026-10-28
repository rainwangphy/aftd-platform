import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTwoFullRootsOverlapEmpty
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints
import AFTD.Kb.Tcs.CyclePowerGapLeftSide
import AFTD.Kb.Tcs.CyclePowerGapRightSide
import AFTD.Kb.Tcs.CyclePowerDyadicFullGapSidesConvex

/-!
# cycle_power_dyadic_full_gap_class_no_island

Topic: combinatorics   Node: 555b968fcd79

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

In a tight exact full ordinary-coverage dyadic model, every class rooted strictly between full roots zero and g has no selected island between missing offsets, when g lies between half and the full radius.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_full_gap_class_no_island
    (m : ℕ) (hm : 1 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p : ℤ, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun i => (x p i).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true)
    (g : ℕ) (hlo : 2^(m-1) ≤ g) (hg : g ≤ 2^m)
    (hfull₀ : ∀ i < 2^m, x 0 i = true)
    (hfullg : ∀ i < 2^m, x (g : ℤ) i = true) :
    ∀ r : ℕ, 0 < r → r < g → ∀ a b c : ℕ, a < b → b < c → c < 2^m →
      x (r : ℤ) a = false → x (r : ℤ) b = true → x (r : ℤ) c = true := by
  classical
  have hconv := cycle_power_dyadic_full_gap_sides_convex m hm x htight hexact hcover
    g hlo hg hfull₀ hfullg
  intro r hr₀ hrg a b c hab hbc hcD hxa hxb
  let q : Fin (g-1) := ⟨r-1, by omega⟩
  have hq : q.val+1 = r := by dsimp [q]; omega
  have hends := cycle_power_dyadic_exact_endpoints m hm x hexact (r : ℤ)
  have hgap := cycle_power_dyadic_two_full_roots_overlap_empty m hm x htight hexact
    g hg hfull₀ hfullg r hr₀ hrg b (by omega) hxb
  rcases hgap with hleft | hright
  · let i : Fin g := ⟨r, hrg⟩
    let j : Fin g := ⟨r+a, by omega⟩
    let k : Fin g := ⟨r+b, hleft⟩
    have hi : i ∈ cycle_power_gap_left_side g r (x (r : ℤ)) := by
      apply mem_filter.mpr
      refine ⟨mem_univ _, le_rfl, ?_⟩
      simpa only [i, Nat.sub_self] using hends.1
    have hk : k ∈ cycle_power_gap_left_side g r (x (r : ℤ)) := by
      apply mem_filter.mpr
      refine ⟨mem_univ _, by dsimp [k]; omega, ?_⟩
      simpa only [k, Nat.add_sub_cancel_left] using hxb
    have hi' : i ∈ cycle_power_gap_left_side g (q.val+1) (x ((q.val+1 : ℕ) : ℤ)) := by simpa only [hq] using hi
    have hk' : k ∈ cycle_power_gap_left_side g (q.val+1) (x ((q.val+1 : ℕ) : ℤ)) := by simpa only [hq] using hk
    have hj := hconv.1 q i j k (by change r ≤ r+a; omega) (by change r+a ≤ r+b; omega) hi' hk'
    have hj' : j ∈ cycle_power_gap_left_side g r (x (r : ℤ)) := by simpa only [hq] using hj
    have he := (mem_filter.mp hj').2.2
    have ha : x (r : ℤ) a = true := by simpa only [j, Nat.add_sub_cancel_left] using he
    rw [hxa] at ha
    contradiction
  · let i : Fin g := ⟨r+b-2^m, by omega⟩
    let j : Fin g := ⟨r+c-2^m, by omega⟩
    let k : Fin g := ⟨r-1, by omega⟩
    have hi : i ∈ cycle_power_gap_right_side (2^m) g r (x (r : ℤ)) := by
      apply mem_filter.mpr
      refine ⟨mem_univ _, by dsimp [i]; omega, ?_⟩
      have he : 2^m+i.val-r = b := by dsimp [i]; omega
      simpa only [he] using hxb
    have hk : k ∈ cycle_power_gap_right_side (2^m) g r (x (r : ℤ)) := by
      apply mem_filter.mpr
      refine ⟨mem_univ _, by dsimp [k]; omega, ?_⟩
      have he : 2^m+k.val-r = 2^m-1 := by dsimp [k]; omega
      simpa only [he] using hends.2
    have hi' : i ∈ cycle_power_gap_right_side (2^m) g (q.val+1) (x ((q.val+1 : ℕ) : ℤ)) := by simpa only [hq] using hi
    have hk' : k ∈ cycle_power_gap_right_side (2^m) g (q.val+1) (x ((q.val+1 : ℕ) : ℤ)) := by simpa only [hq] using hk
    have hj := hconv.2 q i j k (by change r+b-2^m ≤ r+c-2^m; omega)
      (by change r+c-2^m ≤ r-1; omega) hi' hk'
    have hj' : j ∈ cycle_power_gap_right_side (2^m) g r (x (r : ℤ)) := by simpa only [hq] using hj
    have he := (mem_filter.mp hj').2.2
    have hoff : 2^m+j.val-r = c := by dsimp [j]; omega
    simpa only [hoff] using he
