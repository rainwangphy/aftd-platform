import AFTD.Prelude
import AFTD.Kb.Tcs.HammingActiveCoords
import AFTD.Kb.Tcs.HammingExceptionalCoords
import AFTD.Kb.Tcs.HammingAllDistinctCoords
import AFTD.Kb.Tcs.HammingDistEqExceptionalAddAllDistinct
import AFTD.Kb.Tcs.HammingActiveCoordsCard

/-!
# hamming_equilateral_triangle_local_types

Topic: combinatorics   Node: 4c90304e1a29

Provenance: formalization of a published result. Source: arXiv:2610.32789 "Triangle-Free Sets in Exact-Distance Hamming Graphs", Proposition 2.2

Suppose $x, y, z : \mathrm{Fin}\, n \to \alpha$ satisfy $\mathrm{hammingDist}(x, y) = r$, $\mathrm{hammingDist}(x, z) = r$, and $\mathrm{hammingDist}(y, z) = r$. If $a_x, a_y, a_z$ count the coordinates where $x, y, z$ respectively are exceptional and $d$ counts the coordinates where all three symbols are distinct, then $a_x = a_y$, $a_x = a_z$, $2a_x + d = r$, $a_x \le r / 2$, $d = r - 2a_x$, and the size of the active support is $r + a_x$.
-/

private lemma hamming_equilateral_triangle_local_types_exceptional_swap {n : ℕ} {α : Type*} [DecidableEq α] (x y z : Fin n → α) :
    hamming_exceptional_coords x z y = hamming_exceptional_coords x y z := by
  simp only [hamming_exceptional_coords]
  congr 1
  ext i
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, fun h => h2 (h.trans h1.symm)⟩

private lemma hamming_equilateral_triangle_local_types_exceptional_swap' {n : ℕ} {α : Type*} [DecidableEq α] (x y z : Fin n → α) :
    hamming_exceptional_coords y z x = hamming_exceptional_coords y x z := by
  simp only [hamming_exceptional_coords]
  congr 1
  ext i
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, fun h => h2 (h.trans h1.symm)⟩

private lemma hamming_equilateral_triangle_local_types_exceptional_swap23 {n : ℕ} {α : Type*} [DecidableEq α] (a b c : Fin n → α) :
    hamming_exceptional_coords a b c = hamming_exceptional_coords a c b := by
  simp only [hamming_exceptional_coords]
  congr 1
  ext i
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, fun h => h2 (h.trans h1.symm)⟩

private lemma hamming_equilateral_triangle_local_types_all_distinct_swap {n : ℕ} {α : Type*} [DecidableEq α] (x y z : Fin n → α) :
    hamming_all_distinct_coords x z y = hamming_all_distinct_coords x y z := by
  simp only [hamming_all_distinct_coords]
  congr 1
  ext i
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun h => h3 h.symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun h => h3 h.symm⟩

private lemma hamming_equilateral_triangle_local_types_all_distinct_swap' {n : ℕ} {α : Type*} [DecidableEq α] (x y z : Fin n → α) :
    hamming_all_distinct_coords y z x = hamming_all_distinct_coords x y z := by
  simp only [hamming_all_distinct_coords]
  congr 1
  ext i
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun h => h2 h.symm, fun h => h3 h.symm, h1⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h3, fun h => h1 h.symm, fun h => h2 h.symm⟩

/-- Classification of local types in equilateral triangles of Hamming graphs: equal exceptional counts a, 2a + d = r, a ≤ r / 2, d = r - 2a, and active support size r + a. -/
theorem hamming_equilateral_triangle_local_types {n : ℕ} {α : Type*} [DecidableEq α]
    (x y z : Fin n → α) (r : ℕ)
    (hxy : hammingDist x y = r)
    (hxz : hammingDist x z = r)
    (hyz : hammingDist y z = r) :
    let ax := (hamming_exceptional_coords x y z).card
    let ay := (hamming_exceptional_coords y x z).card
    let az := (hamming_exceptional_coords z x y).card
    let d := (hamming_all_distinct_coords x y z).card
    ax = ay ∧ ax = az ∧ 2 * ax + d = r ∧ ax ≤ r / 2 ∧ d = r - 2 * ax ∧
      (hamming_active_coords x y z).card = r + ax := by
  dsimp only
  set ax := (hamming_exceptional_coords x y z).card with hax
  set ay := (hamming_exceptional_coords y x z).card with hay
  set az := (hamming_exceptional_coords z x y).card with haz
  set d := (hamming_all_distinct_coords x y z).card with hd
  have h1 : ax + ay + d = r := by
    rw [hax, hay, hd, ← hxy]
    exact (hamming_dist_eq_exceptional_add_all_distinct x y z).symm
  have h2 : ax + az + d = r := by
    have e1 : (hamming_exceptional_coords x z y).card = ax := by
      rw [hax, hamming_equilateral_triangle_local_types_exceptional_swap x y z]
    have e2 : (hamming_all_distinct_coords x z y).card = d := by
      rw [hd, hamming_equilateral_triangle_local_types_all_distinct_swap x y z]
    rw [← hxz, hamming_dist_eq_exceptional_add_all_distinct x z y, e1, e2]
  have h3 : ay + az + d = r := by
    have e1 : (hamming_exceptional_coords y z x).card = ay := by
      rw [hay, hamming_equilateral_triangle_local_types_exceptional_swap' x y z]
    have e2 : (hamming_exceptional_coords z y x).card = az := by
      rw [haz, hamming_equilateral_triangle_local_types_exceptional_swap23 z y x]
    have e3 : (hamming_all_distinct_coords y z x).card = d := by
      rw [hd, hamming_equilateral_triangle_local_types_all_distinct_swap' x y z]
    rw [← hyz, hamming_dist_eq_exceptional_add_all_distinct y z x, e1, e2, e3]
  have hab : ax = ay := by omega
  have hac : ax = az := by omega
  refine ⟨hab, hac, by omega, by omega, by omega, ?_⟩
  rw [hamming_active_coords_card, ← hax, ← hay, ← haz, ← hd]
  omega
