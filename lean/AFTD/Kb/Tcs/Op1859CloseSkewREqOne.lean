import AFTD.Prelude
import AFTD.Kb.Tcs.HammingCloseSkewSystem

/-!
# op_1859_close_skew_r_eq_one

Topic: combinatorics   Node: a03fe50f1b57

Provenance: formalization of a published result. Source: arXiv:2611.20820 Sec. 5.7, Proposition 4.2

Let n > 1 be a natural number. If v and w are sequences of k points in {0,1}^n forming a close-skew system of radius 1, then k <= 2.
-/

open Finset

private theorem op_1859_close_skew_r_eq_one_triangle_ne_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y z : ι → Bool) (hxy : hammingDist x y = 1) (hyz : hammingDist y z = 1) :
    hammingDist x z ≠ 1 := by
  have h1 : (univ.filter (fun i => x i ≠ y i)).card = 1 := hxy
  have h2 : (univ.filter (fun i => y i ≠ z i)).card = 1 := hyz
  obtain ⟨a, ha⟩ := card_eq_one.mp h1
  obtain ⟨b, hb⟩ := card_eq_one.mp h2
  have hdiff : univ.filter (fun i => x i ≠ z i) =
      symmDiff (univ.filter (fun i => x i ≠ y i)) (univ.filter (fun i => y i ≠ z i)) := by
    ext i
    rw [mem_symmDiff, mem_filter, mem_filter, mem_filter]
    simp only [mem_univ, true_and]
    have hbool : ∀ (u v w : Bool), (u ≠ w) ↔ ((u ≠ v ∧ ¬(v ≠ w)) ∨ (v ≠ w ∧ ¬(u ≠ v))) := by
      decide
    exact hbool (x i) (y i) (z i)
  have hdist : hammingDist x z = (symmDiff ({a} : Finset ι) {b}).card := by
    dsimp [hammingDist]
    rw [hdiff, ha, hb]
  rw [hdist]
  by_cases hab : a = b
  · subst hab
    simp
  · have hdisj : Disjoint ({a} : Finset ι) {b} := by
      rw [disjoint_singleton_left]
      simp [hab]
    rw [symmDiff_eq_union hdisj]
    simp [hab]

/-- The close-skew set-pair bound holds for radius r = 1. -/
theorem op_1859_close_skew_r_eq_one {n k : ℕ} (hn : 1 < n)
    (v w : Fin k → Fin n → Bool) (h : hamming_close_skew_system 1 v w) :
    k ≤ 2 := by
  have _ := hn
  by_contra! hk
  have hi0 : 0 < k := by omega
  have hi1 : 1 < k := by omega
  have hi2 : 2 < k := by omega
  let i0 : Fin k := ⟨0, hi0⟩
  let i1 : Fin k := ⟨1, hi1⟩
  let i2 : Fin k := ⟨2, hi2⟩
  have h01 : i0 < i1 := by simp [i0, i1]
  have h12 : i1 < i2 := by simp [i1, i2]
  have h02 : i0 < i2 := by simp [i0, i2]
  rcases h with ⟨hclose, hfar, hskew⟩
  have hne (i j : Fin k) (hij : j < i) : v i ≠ v j := by
    intro heq
    have h1 := hfar i
    have h2 := hskew i j hij
    rw [heq] at h1
    omega
  have hd01 : hammingDist (v i0) (v i1) = 1 := by
    have hle := hclose i0 i1
    have hne' : v i0 ≠ v i1 := (hne i1 i0 h01).symm
    have hpos := hammingDist_pos.mpr hne'
    omega
  have hd12 : hammingDist (v i1) (v i2) = 1 := by
    have hle := hclose i1 i2
    have hne' : v i1 ≠ v i2 := (hne i2 i1 h12).symm
    have hpos := hammingDist_pos.mpr hne'
    omega
  have hd02 : hammingDist (v i0) (v i2) = 1 := by
    have hle := hclose i0 i2
    have hne' : v i0 ≠ v i2 := (hne i2 i0 h02).symm
    have hpos := hammingDist_pos.mpr hne'
    omega
  have hcontra := op_1859_close_skew_r_eq_one_triangle_ne_one (v i0) (v i1) (v i2) hd01 hd12
  exact hcontra hd02
