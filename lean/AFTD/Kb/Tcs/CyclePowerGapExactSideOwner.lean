import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerExactPairUnique
import AFTD.Kb.Tcs.CyclePowerExactPairExists
import AFTD.Kb.Tcs.CyclePowerGapLeftSide
import AFTD.Kb.Tcs.CyclePowerGapRightSide

/-!
# cycle_power_gap_exact_side_owner

Topic: combinatorics   Node: 5614be122db8

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

Exact distance D-R ownership in an integer model gives unique compressed gap-side owners for every forward distance-R pair on Fin g, when R and g are at most D.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_gap_exact_side_owner
    (D R g : ℕ) (hRD : R ≤ D) (hg : g ≤ D) (x : ℤ → ℕ → Bool)
    (hexact : ∀ v : ℤ, (range R).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-R)).toNat) = 1) :
    ∀ i j : Fin g, j.val+R = i.val → ∃! r : Fin (g-1),
      i ∈ cycle_power_gap_left_side g (r.val+1) (x ((r.val+1 : ℕ) : ℤ)) ∧
      j ∈ cycle_power_gap_right_side D g (r.val+1) (x ((r.val+1 : ℕ) : ℤ)) := by
  intro i j hdist
  obtain ⟨a, ha, h₀, h₁⟩ := cycle_power_exact_pair_exists D R x hexact (i.val : ℤ)
  have hi : i.val < g := i.isLt
  have hj : j.val < g := j.isLt
  let r : Fin (g-1) := ⟨i.val-a-1, by omega⟩
  have hr : r.val+1 = i.val-a := by dsimp [r]; omega
  have hroot : (i.val : ℤ)-(a : ℤ) = ((r.val+1 : ℕ) : ℤ) := by omega
  have ha₀ : i.val-(r.val+1) = a := by omega
  have ha₁ : D+j.val-(r.val+1) = a+D-R := by omega
  have hAr : i ∈ cycle_power_gap_left_side g (r.val+1) (x ((r.val+1 : ℕ) : ℤ)) := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, by omega, ?_⟩
    rw [ha₀]
    simpa only [hroot] using h₀
  have hBr : j ∈ cycle_power_gap_right_side D g (r.val+1) (x ((r.val+1 : ℕ) : ℤ)) := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, by omega, ?_⟩
    rw [ha₁]
    simpa only [hroot] using h₁
  refine ⟨r, ⟨hAr, hBr⟩, ?_⟩
  intro s hs
  have his := (mem_filter.mp hs.1).2
  have hjs := (mem_filter.mp hs.2).2
  let b := i.val-(s.val+1)
  have hb : b < R := by dsimp [b]; omega
  have hroot' : (i.val : ℤ)-(b : ℤ) = ((s.val+1 : ℕ) : ℤ) := by dsimp [b]; omega
  have hboff : b+D-R = D+j.val-(s.val+1) := by dsimp [b]; omega
  have hb₀ : x ((i.val : ℤ)-(b : ℤ)) b = true := by
    simpa only [hroot', b] using his.2
  have hb₁ : x ((i.val : ℤ)-(b : ℤ)) (b+D-R) = true := by
    simpa only [hroot', hboff] using hjs.2
  have he := cycle_power_exact_pair_unique D R x hexact (i.val : ℤ)
    a b ha hb h₀ h₁ hb₀ hb₁
  apply Fin.ext
  dsimp [b] at he
  have hslt : s.val < g-1 := s.isLt
  omega
