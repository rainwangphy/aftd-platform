import AFTD.Prelude
import AFTD.Kb.Tcs.IsReflexivePolytope
import AFTD.Kb.Tcs.P8Polytope
import AFTD.Kb.Tcs.PolytopeConvexFacets
import AFTD.Kb.Tcs.PolytopePolar
import AFTD.Kb.Tcs.P8Vertices
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.IsLatticePolytope
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.G

/-!
# p8_reflexive_with_1371_convex_facets

Topic: combinatorics   Node: 2719c8821b2d

Provenance: formalization of a published result. Source: arXiv:2611.08819, Theorem 2.1

The 8-dimensional polytope P_8 is a reflexive polytope with exactly 44 vertices and exactly 1371 facets, which exceeds 6^(8/2) = 1296, refuting the reflexive facet conjecture in dimension 8.
-/

def in680V3L : List (ℤ × ℤ × ℤ) := [(6,-6,0),(4,0,-2),(3,1,-2),(3,0,0),(3,0,-3),(2,1,-1),(2,-2,2),(1,1,-1),(1,0,1),(1,-1,2),(0,0,-3),(0,-1,2),(0,-3,3),(0,-6,0),(0,-6,-6),(-1,0,0),(-1,0,-1),(-1,-2,2),(-2,-1,-1),(-2,-2,-2),(-3,-3,0)]
def in680W3L : List (ℤ × ℤ × ℤ) := [(-2,-6,-4),(-2,-4,-4),(-2,-4,-2),(-2,-2,-3),(-2,-2,-1),(-2,-1,-2),(-2,-1,-1),(-1,-1,-3),(-1,-1,1),(-1,0,-2),(-1,0,1),(0,-12,-6),(0,-6,-6),(0,-6,0),(0,-2,-4),(0,-2,2),(0,-1,2),(0,1,-1),(0,1,0),(1,-5,2),(1,1,-1),(1,1,0),(2,-2,-4),(2,-1,2),(2,0,-2),(2,0,1),(3,-2,2),(3,-1,1),(4,-8,2),(4,-4,2),(6,-24,-12),(6,-18,-12),(6,-12,0),(6,-6,-6),(6,-6,0),(6,-4,-4),(6,-4,-2)]

def in680vec3 (t : ℤ × ℤ × ℤ) : Fin 3 → ℝ := ![(t.1 : ℝ), (t.2.1 : ℝ), (t.2.2 : ℝ)]

def in680dot3 (t : ℤ × ℤ × ℤ) (y : Fin 3 → ℝ) : ℝ :=
  (t.1 : ℝ) * y 0 + (t.2.1 : ℝ) * y 1 + (t.2.2 : ℝ) * y 2

def in680W3C : Set (Fin 3 → ℝ) := convexHull ℝ (in680vec3 '' {t | t ∈ in680W3L})

theorem in680_W3C_conv : Convex ℝ in680W3C := convex_convexHull _ _

theorem in680_W3C_mem {t : ℤ × ℤ × ℤ} (h : t ∈ in680W3L) : in680vec3 t ∈ in680W3C :=
  subset_convexHull _ _ ⟨t, h, rfl⟩

theorem in680_zero_mem : (0 : Fin 3 → ℝ) ∈ in680W3C := by
  have h1 := in680_W3C_mem (t := (-2,-6,-4)) (by decide +kernel)
  have h2 := in680_W3C_mem (t := (-2,-2,-1)) (by decide +kernel)
  have h3 := in680_W3C_mem (t := (0,1,0)) (by decide +kernel)
  have h4 := in680_W3C_mem (t := (2,-1,2)) (by decide +kernel)
  have hc := in680_W3C_conv
  have h5 := hc.sum_mem (t := Finset.univ) (w := ![(1/19 : ℝ), 2/19, 13/19, 3/19])
    (z := ![in680vec3 (-2,-6,-4), in680vec3 (-2,-2,-1), in680vec3 (0,1,0), in680vec3 (2,-1,2)])
    (by intro i _; fin_cases i <;> simp <;> norm_num)
    (by simp [Fin.sum_univ_succ]; norm_num)
    (by intro i _; fin_cases i <;> simp [h1, h2, h3, h4])
  convert h5 using 1
  funext j
  fin_cases j <;> simp [Fin.sum_univ_succ, in680vec3] <;> norm_num

theorem in680_close (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t) (p q r : ℤ × ℤ × ℤ)
    (hp : p ∈ in680W3L) (hq : q ∈ in680W3L) (hr : r ∈ in680W3L) (α β γ : ℝ)
    (ha : 0 ≤ α) (hb : 0 ≤ β) (hc : 0 ≤ γ) (hs : α + β + γ ≤ t / 6)
    (he : y = α • in680vec3 p + β • in680vec3 q + γ • in680vec3 r) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  have hconv := in680_W3C_conv
  rcases eq_or_lt_of_le ht with h0 | hpos
  · have ht0 : t = 0 := h0.symm
    have ha0 : α = 0 := by rw [ht0] at hs; linarith
    have hb0 : β = 0 := by rw [ht0] at hs; linarith
    have hc0 : γ = 0 := by rw [ht0] at hs; linarith
    refine ⟨0, in680_zero_mem, ?_⟩
    rw [he, ha0, hb0, hc0, ht0]
    simp
  · set σ := t / 6 with hσ
    have hσp : 0 < σ := by positivity
    set c := (α / σ) • in680vec3 p + (β / σ) • in680vec3 q + (γ / σ) • in680vec3 r
      + (1 - (α + β + γ) / σ) • (0 : Fin 3 → ℝ) with hcdef
    have h1 : c ∈ in680W3C := by
      have hrem : 0 ≤ 1 - (α + β + γ) / σ := by
        rw [sub_nonneg, div_le_one hσp]
        exact hs
      have hsum4 := hconv.sum_mem (t := Finset.univ) (w := ![α / σ, β / σ, γ / σ, 1 - (α + β + γ) / σ])
        (z := ![in680vec3 p, in680vec3 q, in680vec3 r, (0 : Fin 3 → ℝ)])
        (by
          intro i _
          fin_cases i
          · exact div_nonneg ha hσp.le
          · exact div_nonneg hb hσp.le
          · exact div_nonneg hc hσp.le
          · exact hrem)
        (by simp [Fin.sum_univ_succ]; field_simp; ring)
        (by
          intro i _
          fin_cases i
          · exact in680_W3C_mem hp
          · exact in680_W3C_mem hq
          · exact in680_W3C_mem hr
          · exact in680_zero_mem)
      convert hsum4 using 1
      simp [Fin.sum_univ_succ, hcdef]
      abel
    refine ⟨c, h1, ?_⟩
    rw [he, hcdef]
    simp only [smul_add, smul_smul]
    have e1 : σ * (α / σ) = α := by field_simp
    have e2 : σ * (β / σ) = β := by field_simp
    have e3 : σ * (γ / σ) = γ := by field_simp
    rw [e1, e2, e3]
    simp
theorem in680fan0 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h1 : 0 ≤ (-2:ℝ) * y 0 + (6:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h2 : 0 ≤ (-3:ℝ) * y 0 + (7:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h3 : 0 ≤ (-3:ℝ) * y 0 + (6:ℝ) * y 1 + (0:ℝ) * y 2)
    (h4 : 0 ≤ (-3:ℝ) * y 0 + (6:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h5 : 0 ≤ (-4:ℝ) * y 0 + (7:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h6 : 0 ≤ (-4:ℝ) * y 0 + (4:ℝ) * y 1 + (2:ℝ) * y 2)
    (h7 : 0 ≤ (-5:ℝ) * y 0 + (7:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h8 : 0 ≤ (-5:ℝ) * y 0 + (6:ℝ) * y 1 + (1:ℝ) * y 2)
    (h9 : 0 ≤ (-5:ℝ) * y 0 + (5:ℝ) * y 1 + (2:ℝ) * y 2)
    (h10 : 0 ≤ (-6:ℝ) * y 0 + (6:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h11 : 0 ≤ (-6:ℝ) * y 0 + (5:ℝ) * y 1 + (2:ℝ) * y 2)
    (h12 : 0 ≤ (-6:ℝ) * y 0 + (3:ℝ) * y 1 + (3:ℝ) * y 2)
    (h13 : 0 ≤ (-6:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h14 : 0 ≤ (-6:ℝ) * y 0 + (0:ℝ) * y 1 + (-6:ℝ) * y 2)
    (h15 : 0 ≤ (-7:ℝ) * y 0 + (6:ℝ) * y 1 + (0:ℝ) * y 2)
    (h16 : 0 ≤ (-7:ℝ) * y 0 + (6:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h17 : 0 ≤ (-7:ℝ) * y 0 + (4:ℝ) * y 1 + (2:ℝ) * y 2)
    (h18 : 0 ≤ (-8:ℝ) * y 0 + (5:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h19 : 0 ≤ (-8:ℝ) * y 0 + (4:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h20 : 0 ≤ (-9:ℝ) * y 0 + (3:ℝ) * y 1 + (0:ℝ) * y 2)
    (hv : -t ≤ (6:ℝ) * y 0 + (-6:ℝ) * y 1 + (0:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((1:ℝ) * y 0 + (-4:ℝ) * y 1 + (1:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (1:ℝ) * y 0 + (-4:ℝ) * y 1 + (1:ℝ) * y 2 := s0
    have ha : 0 ≤ (-1:ℝ) * y 0 + (2:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h3]
    have hb : 0 ≤ (1:ℝ) * y 0 + (-4:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ (-1:ℝ) * y 0 + (3:ℝ) * y 1 + (-1:ℝ) * y 2 := by linarith only [h1]
    refine in680_close y t ht (-1,0,1) (-2,-1,-1) (-2,-1,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((1:ℝ) * y 0 + (-4:ℝ) * y 1 + (1:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((0:ℝ) * y 0 + (-3:ℝ) * y 1 + (0:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (0:ℝ) * y 0 + (-3:ℝ) * y 1 + (0:ℝ) * y 2 := s1
      have ha : 0 ≤ ((-2:ℝ)/3) * y 0 + ((2:ℝ)/3) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [h6]
      have hb : 0 ≤ (0:ℝ) * y 0 + (-1:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((-1:ℝ)/3) * y 0 + ((4:ℝ)/3) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (-1,0,1) (-2,-1,-2) (-1,0,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((0:ℝ) * y 0 + (-3:ℝ) * y 1 + (0:ℝ) * y 2) := by linarith only [s1]
      rcases le_total 0 ((-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2) with s2 | s2
      · have s2p : 0 ≤ (-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2 := s2
        have ha : 0 ≤ ((-2:ℝ)/3) * y 0 + ((1:ℝ)/3) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [h12]
        have hb : 0 ≤ ((-1:ℝ)/3) * y 0 + ((-1:ℝ)/3) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [s2p]
        have hc : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [s1n]
        refine in680_close y t ht (-1,0,1) (-1,0,-2) (0,1,-1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring
      · have s2n : 0 ≤ -((-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2) := by linarith only [s2]
        have ha : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h13]
        have hb : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2 := by linarith only [h14]
        have hc : 0 ≤ (1:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [s2n]
        refine in680_close y t ht (-1,0,1) (0,1,-1) (0,1,0) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan1 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (2:ℝ) * y 0 + (-6:ℝ) * y 1 + (2:ℝ) * y 2)
    (h2 : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h3 : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (2:ℝ) * y 2)
    (h4 : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h5 : 0 ≤ (-2:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h6 : 0 ≤ (-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (4:ℝ) * y 2)
    (h7 : 0 ≤ (-3:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h8 : 0 ≤ (-3:ℝ) * y 0 + (0:ℝ) * y 1 + (3:ℝ) * y 2)
    (h9 : 0 ≤ (-3:ℝ) * y 0 + (-1:ℝ) * y 1 + (4:ℝ) * y 2)
    (h10 : 0 ≤ (-4:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h11 : 0 ≤ (-4:ℝ) * y 0 + (-1:ℝ) * y 1 + (4:ℝ) * y 2)
    (h12 : 0 ≤ (-4:ℝ) * y 0 + (-3:ℝ) * y 1 + (5:ℝ) * y 2)
    (h13 : 0 ≤ (-4:ℝ) * y 0 + (-6:ℝ) * y 1 + (2:ℝ) * y 2)
    (h14 : 0 ≤ (-4:ℝ) * y 0 + (-6:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h15 : 0 ≤ (-5:ℝ) * y 0 + (0:ℝ) * y 1 + (2:ℝ) * y 2)
    (h16 : 0 ≤ (-5:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2)
    (h17 : 0 ≤ (-5:ℝ) * y 0 + (-2:ℝ) * y 1 + (4:ℝ) * y 2)
    (h18 : 0 ≤ (-6:ℝ) * y 0 + (-1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h19 : 0 ≤ (-6:ℝ) * y 0 + (-2:ℝ) * y 1 + (0:ℝ) * y 2)
    (h20 : 0 ≤ (-7:ℝ) * y 0 + (-3:ℝ) * y 1 + (2:ℝ) * y 2)
    (hv : -t ≤ (4:ℝ) * y 0 + (0:ℝ) * y 1 + (-2:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((2:ℝ) * y 0 + (-3:ℝ) * y 1 + (-1:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (2:ℝ) * y 0 + (-3:ℝ) * y 1 + (-1:ℝ) * y 2 := s0
    have ha : 0 ≤ ((-1:ℝ)/3) * y 0 + (0:ℝ) * y 1 + ((2:ℝ)/3) * y 2 := by linarith only [h3]
    have hb : 0 ≤ ((2:ℝ)/3) * y 0 + (-1:ℝ) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h2]
    refine in680_close y t ht (-1,-1,1) (-2,-2,-1) (-2,-1,-1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((2:ℝ) * y 0 + (-3:ℝ) * y 1 + (-1:ℝ) * y 2) := by linarith only [s0]
    have ha : 0 ≤ ((1:ℝ)/3) * y 0 + (-1:ℝ) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [h0]
    have hb : 0 ≤ ((-1:ℝ)/3) * y 0 + (0:ℝ) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h4]
    have hc : 0 ≤ ((-2:ℝ)/3) * y 0 + (1:ℝ) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [s0n]
    refine in680_close y t ht (-1,-1,1) (-2,-1,-1) (-1,0,1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan2 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (3:ℝ) * y 0 + (-7:ℝ) * y 1 + (2:ℝ) * y 2)
    (h1 : 0 ≤ (1:ℝ) * y 0 + (-1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h3 : 0 ≤ (0:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h4 : 0 ≤ (0:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h5 : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2)
    (h6 : 0 ≤ (-1:ℝ) * y 0 + (-3:ℝ) * y 1 + (4:ℝ) * y 2)
    (h7 : 0 ≤ (-2:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2)
    (h8 : 0 ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (3:ℝ) * y 2)
    (h9 : 0 ≤ (-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (4:ℝ) * y 2)
    (h10 : 0 ≤ (-3:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h11 : 0 ≤ (-3:ℝ) * y 0 + (-2:ℝ) * y 1 + (4:ℝ) * y 2)
    (h12 : 0 ≤ (-3:ℝ) * y 0 + (-4:ℝ) * y 1 + (5:ℝ) * y 2)
    (h13 : 0 ≤ (-3:ℝ) * y 0 + (-7:ℝ) * y 1 + (2:ℝ) * y 2)
    (h14 : 0 ≤ (-3:ℝ) * y 0 + (-7:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h15 : 0 ≤ (-4:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h16 : 0 ≤ (-4:ℝ) * y 0 + (-1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h17 : 0 ≤ (-4:ℝ) * y 0 + (-3:ℝ) * y 1 + (4:ℝ) * y 2)
    (h18 : 0 ≤ (-5:ℝ) * y 0 + (-2:ℝ) * y 1 + (1:ℝ) * y 2)
    (h19 : 0 ≤ (-5:ℝ) * y 0 + (-3:ℝ) * y 1 + (0:ℝ) * y 2)
    (h20 : 0 ≤ (-6:ℝ) * y 0 + (-4:ℝ) * y 1 + (2:ℝ) * y 2)
    (hv : -t ≤ (3:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((18:ℝ) * y 0 + (-2:ℝ) * y 1 + (-14:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (18:ℝ) * y 0 + (-2:ℝ) * y 1 + (-14:ℝ) * y 2 := s0
    have ha : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [h5]
    have hb : 0 ≤ ((3:ℝ)/2) * y 0 + ((-1:ℝ)/6) * y 1 + ((-7:ℝ)/6) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [h7]
    refine in680_close y t ht (1,-5,2) (0,-6,0) (-2,-4,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((18:ℝ) * y 0 + (-2:ℝ) * y 1 + (-14:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((9:ℝ) * y 0 + (-3:ℝ) * y 1 + (-12:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (9:ℝ) * y 0 + (-3:ℝ) * y 1 + (-12:ℝ) * y 2 := s1
      have ha : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/9) * y 1 + ((2:ℝ)/9) * y 2 := by linarith only [h3]
      have hb : 0 ≤ ((1:ℝ)/2) * y 0 + ((-1:ℝ)/6) * y 1 + ((-2:ℝ)/3) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ (-1:ℝ) * y 0 + ((1:ℝ)/9) * y 1 + ((7:ℝ)/9) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (1,-5,2) (-2,-4,-2) (-2,-2,-1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((9:ℝ) * y 0 + (-3:ℝ) * y 1 + (-12:ℝ) * y 2) := by linarith only [s1]
      rcases le_total 0 ((-3:ℝ) * y 0 + (-3:ℝ) * y 1 + (-6:ℝ) * y 2) with s2 | s2
      · have s2p : 0 ≤ (-3:ℝ) * y 0 + (-3:ℝ) * y 1 + (-6:ℝ) * y 2 := s2
        have ha : 0 ≤ ((1:ℝ)/6) * y 0 + ((-1:ℝ)/6) * y 1 + (0:ℝ) * y 2 := by linarith only [h1]
        have hb : 0 ≤ ((-1:ℝ)/6) * y 0 + ((-1:ℝ)/6) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [s2p]
        have hc : 0 ≤ ((-1:ℝ)/2) * y 0 + ((1:ℝ)/6) * y 1 + ((2:ℝ)/3) * y 2 := by linarith only [s1n]
        refine in680_close y t ht (1,-5,2) (-2,-2,-1) (-1,-1,1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring
      · have s2n : 0 ≤ -((-3:ℝ) * y 0 + (-3:ℝ) * y 1 + (-6:ℝ) * y 2) := by linarith only [s2]
        have ha : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/3) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h4]
        have hb : 0 ≤ (-1:ℝ) * y 0 + ((-1:ℝ)/3) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h10]
        have hc : 0 ≤ ((1:ℝ)/2) * y 0 + ((1:ℝ)/2) * y 1 + (1:ℝ) * y 2 := by linarith only [s2n]
        refine in680_close y t ht (1,-5,2) (-1,-1,1) (0,-2,2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan3 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (3:ℝ) * y 0 + (-6:ℝ) * y 1 + (0:ℝ) * y 2)
    (h1 : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h2 : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h4 : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h5 : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h6 : 0 ≤ (-1:ℝ) * y 0 + (-2:ℝ) * y 1 + (2:ℝ) * y 2)
    (h7 : 0 ≤ (-2:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h8 : 0 ≤ (-2:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2)
    (h9 : 0 ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h10 : 0 ≤ (-3:ℝ) * y 0 + (0:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h11 : 0 ≤ (-3:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h12 : 0 ≤ (-3:ℝ) * y 0 + (-3:ℝ) * y 1 + (3:ℝ) * y 2)
    (h13 : 0 ≤ (-3:ℝ) * y 0 + (-6:ℝ) * y 1 + (0:ℝ) * y 2)
    (h14 : 0 ≤ (-3:ℝ) * y 0 + (-6:ℝ) * y 1 + (-6:ℝ) * y 2)
    (h15 : 0 ≤ (-4:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h16 : 0 ≤ (-4:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h17 : 0 ≤ (-4:ℝ) * y 0 + (-2:ℝ) * y 1 + (2:ℝ) * y 2)
    (h18 : 0 ≤ (-5:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h19 : 0 ≤ (-5:ℝ) * y 0 + (-2:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h20 : 0 ≤ (-6:ℝ) * y 0 + (-3:ℝ) * y 1 + (0:ℝ) * y 2)
    (hv : -t ≤ (3:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (6:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (6:ℝ) * y 2 := s0
    have ha : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2 := by linarith only [h2]
    have hb : 0 ≤ (-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (3:ℝ) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((1:ℝ)/2) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2 := by linarith only [h1]
    refine in680_close y t ht (-2,-1,-1) (-2,-2,-1) (-2,-4,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (6:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((-2:ℝ) * y 0 + (-6:ℝ) * y 1 + (10:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (-2:ℝ) * y 0 + (-6:ℝ) * y 1 + (10:ℝ) * y 2 := s1
      have ha : 0 ≤ ((-1:ℝ)/2) * y 0 + ((1:ℝ)/2) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [h5]
      have hb : 0 ≤ ((-1:ℝ)/4) * y 0 + ((-3:ℝ)/4) * y 1 + ((5:ℝ)/4) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((1:ℝ)/4) * y 0 + ((1:ℝ)/4) * y 1 + ((-3:ℝ)/4) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (-2,-1,-1) (-2,-4,-2) (-2,-6,-4) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((-2:ℝ) * y 0 + (-6:ℝ) * y 1 + (10:ℝ) * y 2) := by linarith only [s1]
      rcases le_total 0 ((0:ℝ) * y 0 + (-6:ℝ) * y 1 + (6:ℝ) * y 2) with s2 | s2
      · have s2p : 0 ≤ (0:ℝ) * y 0 + (-6:ℝ) * y 1 + (6:ℝ) * y 2 := s2
        have ha : 0 ≤ ((-2:ℝ)/3) * y 0 + (0:ℝ) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [h8]
        have hb : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/2) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [s2p]
        have hc : 0 ≤ ((1:ℝ)/6) * y 0 + ((1:ℝ)/2) * y 1 + ((-5:ℝ)/6) * y 2 := by linarith only [s1n]
        refine in680_close y t ht (-2,-1,-1) (-2,-6,-4) (-2,-4,-4) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring
      · have s2n : 0 ≤ -((0:ℝ) * y 0 + (-6:ℝ) * y 1 + (6:ℝ) * y 2) := by linarith only [s2]
        rcases le_total 0 ((1:ℝ) * y 0 + (-4:ℝ) * y 1 + (2:ℝ) * y 2) with s3 | s3
        · have s3p : 0 ≤ (1:ℝ) * y 0 + (-4:ℝ) * y 1 + (2:ℝ) * y 2 := s3
          have ha : 0 ≤ ((-2:ℝ)/3) * y 0 + ((-1:ℝ)/3) * y 1 + ((2:ℝ)/3) * y 2 := by linarith only [h9]
          have hb : 0 ≤ ((1:ℝ)/6) * y 0 + ((-2:ℝ)/3) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [s3p]
          have hc : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2 := by linarith only [s2n]
          refine in680_close y t ht (-2,-1,-1) (-2,-4,-4) (-2,-2,-3) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
          · linarith only [hv]
          · funext i; fin_cases i <;> simp [in680vec3] <;> ring
        · have s3n : 0 ≤ -((1:ℝ) * y 0 + (-4:ℝ) * y 1 + (2:ℝ) * y 2) := by linarith only [s3]
          have ha : 0 ≤ ((-1:ℝ)/2) * y 0 + (-1:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [h6]
          have hb : 0 ≤ ((1:ℝ)/2) * y 0 + (-1:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h0]
          have hc : 0 ≤ ((-1:ℝ)/2) * y 0 + (2:ℝ) * y 1 + (-1:ℝ) * y 2 := by linarith only [s3n]
          refine in680_close y t ht (-2,-1,-1) (-2,-2,-3) (-2,-1,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
          · linarith only [hv]
          · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan4 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (3:ℝ) * y 0 + (-6:ℝ) * y 1 + (3:ℝ) * y 2)
    (h1 : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2)
    (h2 : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h3 : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + (3:ℝ) * y 2)
    (h5 : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h6 : 0 ≤ (-1:ℝ) * y 0 + (-2:ℝ) * y 1 + (5:ℝ) * y 2)
    (h7 : 0 ≤ (-2:ℝ) * y 0 + (1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h8 : 0 ≤ (-2:ℝ) * y 0 + (0:ℝ) * y 1 + (4:ℝ) * y 2)
    (h9 : 0 ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (5:ℝ) * y 2)
    (h10 : 0 ≤ (-3:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h11 : 0 ≤ (-3:ℝ) * y 0 + (-1:ℝ) * y 1 + (5:ℝ) * y 2)
    (h12 : 0 ≤ (-3:ℝ) * y 0 + (-3:ℝ) * y 1 + (6:ℝ) * y 2)
    (h13 : 0 ≤ (-3:ℝ) * y 0 + (-6:ℝ) * y 1 + (3:ℝ) * y 2)
    (h14 : 0 ≤ (-3:ℝ) * y 0 + (-6:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h15 : 0 ≤ (-4:ℝ) * y 0 + (0:ℝ) * y 1 + (3:ℝ) * y 2)
    (h16 : 0 ≤ (-4:ℝ) * y 0 + (0:ℝ) * y 1 + (2:ℝ) * y 2)
    (h17 : 0 ≤ (-4:ℝ) * y 0 + (-2:ℝ) * y 1 + (5:ℝ) * y 2)
    (h18 : 0 ≤ (-5:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h19 : 0 ≤ (-5:ℝ) * y 0 + (-2:ℝ) * y 1 + (1:ℝ) * y 2)
    (h20 : 0 ≤ (-6:ℝ) * y 0 + (-3:ℝ) * y 1 + (3:ℝ) * y 2)
    (hv : -t ≤ (3:ℝ) * y 0 + (0:ℝ) * y 1 + (-3:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (-2:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (-2:ℝ) * y 2 := s0
    have ha : 0 ≤ ((1:ℝ)/2) * y 0 + (0:ℝ) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [h1]
    have hb : 0 ≤ (-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [h2]
    refine in680_close y t ht (0,-2,2) (-1,-1,1) (-1,0,1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (-2:ℝ) * y 2) := by linarith only [s0]
    have ha : 0 ≤ ((-1:ℝ)/2) * y 0 + (-1:ℝ) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [h14]
    have hb : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h10]
    have hc : 0 ≤ (1:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [s0n]
    refine in680_close y t ht (0,-2,2) (-1,0,1) (0,-1,2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan5 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (4:ℝ) * y 0 + (-7:ℝ) * y 1 + (1:ℝ) * y 2)
    (h1 : 0 ≤ (2:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h2 : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h3 : 0 ≤ (1:ℝ) * y 0 + (-1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h4 : 0 ≤ (1:ℝ) * y 0 + (-1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h6 : 0 ≤ (0:ℝ) * y 0 + (-3:ℝ) * y 1 + (3:ℝ) * y 2)
    (h7 : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h8 : 0 ≤ (-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h9 : 0 ≤ (-1:ℝ) * y 0 + (-2:ℝ) * y 1 + (3:ℝ) * y 2)
    (h10 : 0 ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h11 : 0 ≤ (-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (3:ℝ) * y 2)
    (h12 : 0 ≤ (-2:ℝ) * y 0 + (-4:ℝ) * y 1 + (4:ℝ) * y 2)
    (h13 : 0 ≤ (-2:ℝ) * y 0 + (-7:ℝ) * y 1 + (1:ℝ) * y 2)
    (h14 : 0 ≤ (-2:ℝ) * y 0 + (-7:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h15 : 0 ≤ (-3:ℝ) * y 0 + (-1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h16 : 0 ≤ (-3:ℝ) * y 0 + (-1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h17 : 0 ≤ (-3:ℝ) * y 0 + (-3:ℝ) * y 1 + (3:ℝ) * y 2)
    (h18 : 0 ≤ (-4:ℝ) * y 0 + (-2:ℝ) * y 1 + (0:ℝ) * y 2)
    (h19 : 0 ≤ (-4:ℝ) * y 0 + (-3:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h20 : 0 ≤ (-5:ℝ) * y 0 + (-4:ℝ) * y 1 + (1:ℝ) * y 2)
    (hv : -t ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((0:ℝ) * y 0 + (12:ℝ) * y 1 + (-24:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (0:ℝ) * y 0 + (12:ℝ) * y 1 + (-24:ℝ) * y 2 := s0
    have ha : 0 ≤ ((1:ℝ)/6) * y 0 + ((-1:ℝ)/6) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [h3]
    have hb : 0 ≤ (0:ℝ) * y 0 + ((1:ℝ)/2) * y 1 + (-1:ℝ) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((-1:ℝ)/2) * y 0 + ((-1:ℝ)/2) * y 1 + (1:ℝ) * y 2 := by linarith only [h8]
    refine in680_close y t ht (0,-12,-6) (-2,-6,-4) (-2,-4,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((0:ℝ) * y 0 + (12:ℝ) * y 1 + (-24:ℝ) * y 2) := by linarith only [s0]
    have ha : 0 ≤ ((1:ℝ)/6) * y 0 + (0:ℝ) * y 1 + ((-1:ℝ)/6) * y 2 := by linarith only [h2]
    have hb : 0 ≤ ((-1:ℝ)/2) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h7]
    have hc : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/6) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [s0n]
    refine in680_close y t ht (0,-12,-6) (-2,-4,-2) (0,-6,0) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan6 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (4:ℝ) * y 0 + (-4:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h1 : 0 ≤ (2:ℝ) * y 0 + (2:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h2 : 0 ≤ (1:ℝ) * y 0 + (3:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h3 : 0 ≤ (1:ℝ) * y 0 + (2:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h4 : 0 ≤ (1:ℝ) * y 0 + (2:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h5 : 0 ≤ (0:ℝ) * y 0 + (3:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h7 : 0 ≤ (-1:ℝ) * y 0 + (3:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h8 : 0 ≤ (-1:ℝ) * y 0 + (2:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h9 : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h10 : 0 ≤ (-2:ℝ) * y 0 + (2:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h11 : 0 ≤ (-2:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h12 : 0 ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h13 : 0 ≤ (-2:ℝ) * y 0 + (-4:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h14 : 0 ≤ (-2:ℝ) * y 0 + (-4:ℝ) * y 1 + (-8:ℝ) * y 2)
    (h15 : 0 ≤ (-3:ℝ) * y 0 + (2:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h16 : 0 ≤ (-3:ℝ) * y 0 + (2:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h17 : 0 ≤ (-3:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h18 : 0 ≤ (-4:ℝ) * y 0 + (1:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h19 : 0 ≤ (-4:ℝ) * y 0 + (0:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h20 : 0 ≤ (-5:ℝ) * y 0 + (-1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (hv : -t ≤ (2:ℝ) * y 0 + (-2:ℝ) * y 1 + (2:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((1:ℝ) * y 0 + (-4:ℝ) * y 1 + (1:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (1:ℝ) * y 0 + (-4:ℝ) * y 1 + (1:ℝ) * y 2 := s0
    have ha : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h9]
    have hb : 0 ≤ ((1:ℝ)/3) * y 0 + ((-4:ℝ)/3) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((1:ℝ)/3) * y 0 + ((2:ℝ)/3) * y 1 + ((-2:ℝ)/3) * y 2 := by linarith only [h3]
    refine in680_close y t ht (-2,-1,-2) (-2,-2,-3) (-1,-1,-3) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((1:ℝ) * y 0 + (-4:ℝ) * y 1 + (1:ℝ) * y 2) := by linarith only [s0]
    have ha : 0 ≤ ((-2:ℝ)/3) * y 0 + ((-1:ℝ)/3) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [h12]
    have hb : 0 ≤ ((2:ℝ)/3) * y 0 + ((-2:ℝ)/3) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h0]
    have hc : 0 ≤ ((-1:ℝ)/3) * y 0 + ((4:ℝ)/3) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [s0n]
    refine in680_close y t ht (-2,-1,-2) (-1,-1,-3) (-1,0,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan7 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (5:ℝ) * y 0 + (-7:ℝ) * y 1 + (1:ℝ) * y 2)
    (h1 : 0 ≤ (3:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h2 : 0 ≤ (2:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h3 : 0 ≤ (2:ℝ) * y 0 + (-1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h4 : 0 ≤ (2:ℝ) * y 0 + (-1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h5 : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h6 : 0 ≤ (1:ℝ) * y 0 + (-3:ℝ) * y 1 + (3:ℝ) * y 2)
    (h8 : 0 ≤ (0:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h9 : 0 ≤ (0:ℝ) * y 0 + (-2:ℝ) * y 1 + (3:ℝ) * y 2)
    (h10 : 0 ≤ (-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h11 : 0 ≤ (-1:ℝ) * y 0 + (-2:ℝ) * y 1 + (3:ℝ) * y 2)
    (h12 : 0 ≤ (-1:ℝ) * y 0 + (-4:ℝ) * y 1 + (4:ℝ) * y 2)
    (h13 : 0 ≤ (-1:ℝ) * y 0 + (-7:ℝ) * y 1 + (1:ℝ) * y 2)
    (h14 : 0 ≤ (-1:ℝ) * y 0 + (-7:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h15 : 0 ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h16 : 0 ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h17 : 0 ≤ (-2:ℝ) * y 0 + (-3:ℝ) * y 1 + (3:ℝ) * y 2)
    (h18 : 0 ≤ (-3:ℝ) * y 0 + (-2:ℝ) * y 1 + (0:ℝ) * y 2)
    (h19 : 0 ≤ (-3:ℝ) * y 0 + (-3:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h20 : 0 ≤ (-4:ℝ) * y 0 + (-4:ℝ) * y 1 + (1:ℝ) * y 2)
    (hv : -t ≤ (1:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((72:ℝ) * y 0 + (36:ℝ) * y 1 + (-72:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (72:ℝ) * y 0 + (36:ℝ) * y 1 + (-72:ℝ) * y 2 := s0
    have ha : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/12) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [h8]
    have hb : 0 ≤ ((1:ℝ)/6) * y 0 + ((1:ℝ)/12) * y 1 + ((-1:ℝ)/6) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((-1:ℝ)/3) * y 0 + ((-1:ℝ)/6) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [h15]
    refine in680_close y t ht (6,-12,0) (6,-24,-12) (0,-12,-6) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((72:ℝ) * y 0 + (36:ℝ) * y 1 + (-72:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((0:ℝ) * y 0 + (0:ℝ) * y 1 + (-36:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + (-36:ℝ) * y 2 := s1
      have ha : 0 ≤ ((1:ℝ)/6) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h5]
      have hb : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + ((-1:ℝ)/6) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((-1:ℝ)/3) * y 0 + ((-1:ℝ)/6) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (6,-12,0) (0,-12,-6) (0,-6,0) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((0:ℝ) * y 0 + (0:ℝ) * y 1 + (-36:ℝ) * y 2) := by linarith only [s1]
      rcases le_total 0 ((-24:ℝ) * y 0 + (-12:ℝ) * y 1 + (-18:ℝ) * y 2) with s2 | s2
      · have s2p : 0 ≤ (-24:ℝ) * y 0 + (-12:ℝ) * y 1 + (-18:ℝ) * y 2 := s2
        have ha : 0 ≤ ((1:ℝ)/6) * y 0 + (0:ℝ) * y 1 + ((-1:ℝ)/12) * y 2 := by linarith only [h2]
        have hb : 0 ≤ ((-1:ℝ)/3) * y 0 + ((-1:ℝ)/6) * y 1 + ((-1:ℝ)/4) * y 2 := by linarith only [s2p]
        have hc : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [s1n]
        refine in680_close y t ht (6,-12,0) (0,-6,0) (1,-5,2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring
      · have s2n : 0 ≤ -((-24:ℝ) * y 0 + (-12:ℝ) * y 1 + (-18:ℝ) * y 2) := by linarith only [s2]
        have ha : 0 ≤ ((-1:ℝ)/6) * y 0 + ((-1:ℝ)/6) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h10]
        have hb : 0 ≤ ((-2:ℝ)/3) * y 0 + ((-1:ℝ)/3) * y 1 + (0:ℝ) * y 2 := by linarith only [h16]
        have hc : 0 ≤ ((2:ℝ)/3) * y 0 + ((1:ℝ)/3) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [s2n]
        refine in680_close y t ht (6,-12,0) (1,-5,2) (4,-8,2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan8 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (5:ℝ) * y 0 + (-6:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h1 : 0 ≤ (3:ℝ) * y 0 + (0:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h2 : 0 ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h3 : 0 ≤ (2:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h4 : 0 ≤ (2:ℝ) * y 0 + (0:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h5 : 0 ≤ (1:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h6 : 0 ≤ (1:ℝ) * y 0 + (-2:ℝ) * y 1 + (1:ℝ) * y 2)
    (h7 : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h9 : 0 ≤ (0:ℝ) * y 0 + (-1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h10 : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h11 : 0 ≤ (-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h12 : 0 ≤ (-1:ℝ) * y 0 + (-3:ℝ) * y 1 + (2:ℝ) * y 2)
    (h13 : 0 ≤ (-1:ℝ) * y 0 + (-6:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h14 : 0 ≤ (-1:ℝ) * y 0 + (-6:ℝ) * y 1 + (-7:ℝ) * y 2)
    (h15 : 0 ≤ (-2:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h16 : 0 ≤ (-2:ℝ) * y 0 + (0:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h17 : 0 ≤ (-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (1:ℝ) * y 2)
    (h18 : 0 ≤ (-3:ℝ) * y 0 + (-1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h19 : 0 ≤ (-3:ℝ) * y 0 + (-2:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h20 : 0 ≤ (-4:ℝ) * y 0 + (-3:ℝ) * y 1 + (-1:ℝ) * y 2)
    (hv : -t ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((24:ℝ) * y 0 + (48:ℝ) * y 1 + (-60:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (24:ℝ) * y 0 + (48:ℝ) * y 1 + (-60:ℝ) * y 2 := s0
    have ha : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/6) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [h9]
    have hb : 0 ≤ ((1:ℝ)/3) * y 0 + ((2:ℝ)/3) * y 1 + ((-5:ℝ)/6) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((-1:ℝ)/2) * y 0 + ((-1:ℝ)/2) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [h11]
    refine in680_close y t ht (6,-18,-12) (0,-6,-6) (-2,-4,-4) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((24:ℝ) * y 0 + (48:ℝ) * y 1 + (-60:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((0:ℝ) * y 0 + (48:ℝ) * y 1 + (-72:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (0:ℝ) * y 0 + (48:ℝ) * y 1 + (-72:ℝ) * y 2 := s1
      have ha : 0 ≤ ((1:ℝ)/12) * y 0 + (0:ℝ) * y 1 + ((-1:ℝ)/24) * y 2 := by linarith only [h3]
      have hb : 0 ≤ (0:ℝ) * y 0 + ((1:ℝ)/2) * y 1 + ((-3:ℝ)/4) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((-1:ℝ)/4) * y 0 + ((-1:ℝ)/2) * y 1 + ((5:ℝ)/8) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (6,-18,-12) (-2,-4,-4) (-2,-6,-4) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((0:ℝ) * y 0 + (48:ℝ) * y 1 + (-72:ℝ) * y 2) := by linarith only [s1]
      rcases le_total 0 ((-36:ℝ) * y 0 + (36:ℝ) * y 1 + (-72:ℝ) * y 2) with s2 | s2
      · have s2p : 0 ≤ (-36:ℝ) * y 0 + (36:ℝ) * y 1 + (-72:ℝ) * y 2 := s2
        have ha : 0 ≤ ((1:ℝ)/12) * y 0 + ((1:ℝ)/12) * y 1 + ((-1:ℝ)/6) * y 2 := by linarith only [h5]
        have hb : 0 ≤ ((-1:ℝ)/4) * y 0 + ((1:ℝ)/4) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [s2p]
        have hc : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/3) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [s1n]
        refine in680_close y t ht (6,-18,-12) (-2,-6,-4) (0,-12,-6) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring
      · have s2n : 0 ≤ -((-36:ℝ) * y 0 + (36:ℝ) * y 1 + (-72:ℝ) * y 2) := by linarith only [s2]
        have ha : 0 ≤ (0:ℝ) * y 0 + ((1:ℝ)/6) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h7]
        have hb : 0 ≤ ((-1:ℝ)/3) * y 0 + (0:ℝ) * y 1 + ((-1:ℝ)/6) * y 2 := by linarith only [h15]
        have hc : 0 ≤ ((1:ℝ)/6) * y 0 + ((-1:ℝ)/6) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [s2n]
        refine in680_close y t ht (6,-18,-12) (0,-12,-6) (6,-24,-12) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan9 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (5:ℝ) * y 0 + (-5:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h1 : 0 ≤ (3:ℝ) * y 0 + (1:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h2 : 0 ≤ (2:ℝ) * y 0 + (2:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h3 : 0 ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h4 : 0 ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h5 : 0 ≤ (1:ℝ) * y 0 + (2:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h6 : 0 ≤ (1:ℝ) * y 0 + (-1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h7 : 0 ≤ (0:ℝ) * y 0 + (2:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h8 : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h10 : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h11 : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h12 : 0 ≤ (-1:ℝ) * y 0 + (-2:ℝ) * y 1 + (1:ℝ) * y 2)
    (h13 : 0 ≤ (-1:ℝ) * y 0 + (-5:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h14 : 0 ≤ (-1:ℝ) * y 0 + (-5:ℝ) * y 1 + (-8:ℝ) * y 2)
    (h15 : 0 ≤ (-2:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h16 : 0 ≤ (-2:ℝ) * y 0 + (1:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h17 : 0 ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h18 : 0 ≤ (-3:ℝ) * y 0 + (0:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h19 : 0 ≤ (-3:ℝ) * y 0 + (-1:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h20 : 0 ≤ (-4:ℝ) * y 0 + (-2:ℝ) * y 1 + (-2:ℝ) * y 2)
    (hv : -t ≤ (1:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-8:ℝ) * y 0 + (2:ℝ) * y 1 + (2:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-8:ℝ) * y 0 + (2:ℝ) * y 1 + (2:ℝ) * y 2 := s0
    have ha : 0 ≤ ((2:ℝ)/3) * y 0 + ((1:ℝ)/3) * y 1 + ((-2:ℝ)/3) * y 2 := by linarith only [h3]
    have hb : 0 ≤ ((-4:ℝ)/3) * y 0 + ((1:ℝ)/3) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((1:ℝ)/2) * y 0 + ((-1:ℝ)/2) * y 1 + (0:ℝ) * y 2 := by linarith only [h6]
    refine in680_close y t ht (-1,-1,-3) (-2,-2,-3) (-2,-4,-4) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-8:ℝ) * y 0 + (2:ℝ) * y 1 + (2:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((-12:ℝ) * y 0 + (-6:ℝ) * y 1 + (6:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (-12:ℝ) * y 0 + (-6:ℝ) * y 1 + (6:ℝ) * y 2 := s1
      have ha : 0 ≤ (0:ℝ) * y 0 + ((1:ℝ)/2) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [h8]
      have hb : 0 ≤ ((-1:ℝ)/2) * y 0 + ((-1:ℝ)/4) * y 1 + ((1:ℝ)/4) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((1:ℝ)/3) * y 0 + ((-1:ℝ)/12) * y 1 + ((-1:ℝ)/12) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (-1,-1,-3) (-2,-4,-4) (0,-6,-6) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((-12:ℝ) * y 0 + (-6:ℝ) * y 1 + (6:ℝ) * y 2) := by linarith only [s1]
      have ha : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h11]
      have hb : 0 ≤ ((-1:ℝ)/6) * y 0 + ((-1:ℝ)/3) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [h12]
      have hc : 0 ≤ (1:ℝ) * y 0 + ((1:ℝ)/2) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [s1n]
      refine in680_close y t ht (-1,-1,-3) (0,-6,-6) (0,-2,-4) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan10 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (6:ℝ) * y 0 + (-6:ℝ) * y 1 + (3:ℝ) * y 2)
    (h1 : 0 ≤ (4:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2)
    (h2 : 0 ≤ (3:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h3 : 0 ≤ (3:ℝ) * y 0 + (0:ℝ) * y 1 + (3:ℝ) * y 2)
    (h4 : 0 ≤ (3:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h5 : 0 ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h6 : 0 ≤ (2:ℝ) * y 0 + (-2:ℝ) * y 1 + (5:ℝ) * y 2)
    (h7 : 0 ≤ (1:ℝ) * y 0 + (1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h8 : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (4:ℝ) * y 2)
    (h9 : 0 ≤ (1:ℝ) * y 0 + (-1:ℝ) * y 1 + (5:ℝ) * y 2)
    (h11 : 0 ≤ (0:ℝ) * y 0 + (-1:ℝ) * y 1 + (5:ℝ) * y 2)
    (h12 : 0 ≤ (0:ℝ) * y 0 + (-3:ℝ) * y 1 + (6:ℝ) * y 2)
    (h13 : 0 ≤ (0:ℝ) * y 0 + (-6:ℝ) * y 1 + (3:ℝ) * y 2)
    (h14 : 0 ≤ (0:ℝ) * y 0 + (-6:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h15 : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (3:ℝ) * y 2)
    (h16 : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (2:ℝ) * y 2)
    (h17 : 0 ≤ (-1:ℝ) * y 0 + (-2:ℝ) * y 1 + (5:ℝ) * y 2)
    (h18 : 0 ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h19 : 0 ≤ (-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (1:ℝ) * y 2)
    (h20 : 0 ≤ (-3:ℝ) * y 0 + (-3:ℝ) * y 1 + (3:ℝ) * y 2)
    (hv : -t ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + (-3:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-12:ℝ) * y 0 + (-8:ℝ) * y 1 + (-8:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-12:ℝ) * y 0 + (-8:ℝ) * y 1 + (-8:ℝ) * y 2 := s0
    have ha : 0 ≤ ((1:ℝ)/2) * y 0 + ((1:ℝ)/6) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [h2]
    have hb : 0 ≤ (-1:ℝ) * y 0 + ((-2:ℝ)/3) * y 1 + ((-2:ℝ)/3) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((1:ℝ)/2) * y 0 + ((1:ℝ)/2) * y 1 + (1:ℝ) * y 2 := by linarith only [h7]
    refine in680_close y t ht (4,-8,2) (1,-5,2) (0,-2,2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-12:ℝ) * y 0 + (-8:ℝ) * y 1 + (-8:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((-14:ℝ) * y 0 + (-8:ℝ) * y 1 + (-4:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (-14:ℝ) * y 0 + (-8:ℝ) * y 1 + (-4:ℝ) * y 2 := s1
      have ha : 0 ≤ ((1:ℝ)/4) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h4]
      have hb : 0 ≤ ((-7:ℝ)/4) * y 0 + (-1:ℝ) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((3:ℝ)/2) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (4,-8,2) (0,-2,2) (0,-1,2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((-14:ℝ) * y 0 + (-8:ℝ) * y 1 + (-4:ℝ) * y 2) := by linarith only [s1]
      rcases le_total 0 ((-14:ℝ) * y 0 + (-4:ℝ) * y 1 + (12:ℝ) * y 2) with s2 | s2
      · have s2p : 0 ≤ (-14:ℝ) * y 0 + (-4:ℝ) * y 1 + (12:ℝ) * y 2 := s2
        have ha : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/7) * y 1 + ((-1:ℝ)/14) * y 2 := by linarith only [h14]
        have hb : 0 ≤ ((-1:ℝ)/2) * y 0 + ((-1:ℝ)/7) * y 1 + ((3:ℝ)/7) * y 2 := by linarith only [s2p]
        have hc : 0 ≤ ((1:ℝ)/2) * y 0 + ((2:ℝ)/7) * y 1 + ((1:ℝ)/7) * y 2 := by linarith only [s1n]
        refine in680_close y t ht (4,-8,2) (0,-1,2) (2,-1,2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring
      · have s2n : 0 ≤ -((-14:ℝ) * y 0 + (-4:ℝ) * y 1 + (12:ℝ) * y 2) := by linarith only [s2]
        rcases le_total 0 ((-12:ℝ) * y 0 + (-2:ℝ) * y 1 + (16:ℝ) * y 2) with s3 | s3
        · have s3p : 0 ≤ (-12:ℝ) * y 0 + (-2:ℝ) * y 1 + (16:ℝ) * y 2 := s3
          have ha : 0 ≤ ((-1:ℝ)/5) * y 0 + ((-1:ℝ)/5) * y 1 + ((1:ℝ)/10) * y 2 := by linarith only [h19]
          have hb : 0 ≤ ((-6:ℝ)/5) * y 0 + ((-1:ℝ)/5) * y 1 + ((8:ℝ)/5) * y 2 := by linarith only [s3p]
          have hc : 0 ≤ ((7:ℝ)/5) * y 0 + ((2:ℝ)/5) * y 1 + ((-6:ℝ)/5) * y 2 := by linarith only [s2n]
          refine in680_close y t ht (4,-8,2) (2,-1,2) (3,-2,2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
          · linarith only [hv]
          · funext i; fin_cases i <;> simp [in680vec3] <;> ring
        · have s3n : 0 ≤ -((-12:ℝ) * y 0 + (-2:ℝ) * y 1 + (16:ℝ) * y 2) := by linarith only [s3]
          have ha : 0 ≤ ((-1:ℝ)/2) * y 0 + ((-1:ℝ)/4) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [h18]
          have hb : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (2:ℝ) * y 2 := by linarith only [h16]
          have hc : 0 ≤ ((3:ℝ)/2) * y 0 + ((1:ℝ)/4) * y 1 + (-2:ℝ) * y 2 := by linarith only [s3n]
          refine in680_close y t ht (4,-8,2) (3,-2,2) (4,-4,2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
          · linarith only [hv]
          · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan11 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (6:ℝ) * y 0 + (-5:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h1 : 0 ≤ (4:ℝ) * y 0 + (1:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h2 : 0 ≤ (3:ℝ) * y 0 + (2:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h3 : 0 ≤ (3:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h4 : 0 ≤ (3:ℝ) * y 0 + (1:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h5 : 0 ≤ (2:ℝ) * y 0 + (2:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h6 : 0 ≤ (2:ℝ) * y 0 + (-1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h7 : 0 ≤ (1:ℝ) * y 0 + (2:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h8 : 0 ≤ (1:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h9 : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h10 : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h12 : 0 ≤ (0:ℝ) * y 0 + (-2:ℝ) * y 1 + (1:ℝ) * y 2)
    (h13 : 0 ≤ (0:ℝ) * y 0 + (-5:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h14 : 0 ≤ (0:ℝ) * y 0 + (-5:ℝ) * y 1 + (-8:ℝ) * y 2)
    (h15 : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h16 : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h17 : 0 ≤ (-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h18 : 0 ≤ (-2:ℝ) * y 0 + (0:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h19 : 0 ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h20 : 0 ≤ (-3:ℝ) * y 0 + (-2:ℝ) * y 1 + (-2:ℝ) * y 2)
    (hv : -t ≤ (0:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((12:ℝ) * y 0 + (24:ℝ) * y 1 + (-12:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (12:ℝ) * y 0 + (24:ℝ) * y 1 + (-12:ℝ) * y 2 := s0
    have ha : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/3) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [h12]
    have hb : 0 ≤ ((1:ℝ)/2) * y 0 + (1:ℝ) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((-1:ℝ)/2) * y 0 + ((-1:ℝ)/2) * y 1 + (0:ℝ) * y 2 := by linarith only [h17]
    refine in680_close y t ht (6,-6,-6) (2,-2,-4) (0,-2,-4) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((12:ℝ) * y 0 + (24:ℝ) * y 1 + (-12:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((0:ℝ) * y 0 + (36:ℝ) * y 1 + (-36:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (0:ℝ) * y 0 + (36:ℝ) * y 1 + (-36:ℝ) * y 2 := s1
      have ha : 0 ≤ ((1:ℝ)/6) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h9]
      have hb : 0 ≤ (0:ℝ) * y 0 + ((1:ℝ)/2) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((-1:ℝ)/6) * y 0 + ((-1:ℝ)/3) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (6,-6,-6) (0,-2,-4) (0,-6,-6) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((0:ℝ) * y 0 + (36:ℝ) * y 1 + (-36:ℝ) * y 2) := by linarith only [s1]
      have ha : 0 ≤ ((1:ℝ)/6) * y 0 + ((1:ℝ)/6) * y 1 + ((-1:ℝ)/6) * y 2 := by linarith only [h8]
      have hb : 0 ≤ ((-1:ℝ)/6) * y 0 + ((1:ℝ)/6) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h15]
      have hc : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/6) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [s1n]
      refine in680_close y t ht (6,-6,-6) (0,-6,-6) (6,-18,-12) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan12 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (6:ℝ) * y 0 + (-3:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h1 : 0 ≤ (4:ℝ) * y 0 + (3:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h2 : 0 ≤ (3:ℝ) * y 0 + (4:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h3 : 0 ≤ (3:ℝ) * y 0 + (3:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h4 : 0 ≤ (3:ℝ) * y 0 + (3:ℝ) * y 1 + (-6:ℝ) * y 2)
    (h5 : 0 ≤ (2:ℝ) * y 0 + (4:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h6 : 0 ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h7 : 0 ≤ (1:ℝ) * y 0 + (4:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h8 : 0 ≤ (1:ℝ) * y 0 + (3:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h9 : 0 ≤ (1:ℝ) * y 0 + (2:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h10 : 0 ≤ (0:ℝ) * y 0 + (3:ℝ) * y 1 + (-6:ℝ) * y 2)
    (h11 : 0 ≤ (0:ℝ) * y 0 + (2:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h13 : 0 ≤ (0:ℝ) * y 0 + (-3:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h14 : 0 ≤ (0:ℝ) * y 0 + (-3:ℝ) * y 1 + (-9:ℝ) * y 2)
    (h15 : 0 ≤ (-1:ℝ) * y 0 + (3:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h16 : 0 ≤ (-1:ℝ) * y 0 + (3:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h17 : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h18 : 0 ≤ (-2:ℝ) * y 0 + (2:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h19 : 0 ≤ (-2:ℝ) * y 0 + (1:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h20 : 0 ≤ (-3:ℝ) * y 0 + (0:ℝ) * y 1 + (-3:ℝ) * y 2)
    (hv : -t ≤ (0:ℝ) * y 0 + (-3:ℝ) * y 1 + (3:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-2:ℝ) * y 0 + (3:ℝ) * y 1 + (1:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-2:ℝ) * y 0 + (3:ℝ) * y 1 + (1:ℝ) * y 2 := s0
    have ha : 0 ≤ (1:ℝ) * y 0 + ((-1:ℝ)/2) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [h0]
    have hb : 0 ≤ (-1:ℝ) * y 0 + ((3:ℝ)/2) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/2) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [h13]
    refine in680_close y t ht (1,1,-1) (0,1,-1) (-1,0,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-2:ℝ) * y 0 + (3:ℝ) * y 1 + (1:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((-4:ℝ) * y 0 + (4:ℝ) * y 1 + (0:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (-4:ℝ) * y 0 + (4:ℝ) * y 1 + (0:ℝ) * y 2 := s1
      have ha : 0 ≤ ((1:ℝ)/2) * y 0 + ((1:ℝ)/4) * y 1 + ((-1:ℝ)/4) * y 2 := by linarith only [h6]
      have hb : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((1:ℝ)/2) * y 0 + ((-3:ℝ)/4) * y 1 + ((-1:ℝ)/4) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (1,1,-1) (-1,0,-2) (-1,-1,-3) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((-4:ℝ) * y 0 + (4:ℝ) * y 1 + (0:ℝ) * y 2) := by linarith only [s1]
      rcases le_total 0 ((-6:ℝ) * y 0 + (4:ℝ) * y 1 + (-2:ℝ) * y 2) with s2 | s2
      · have s2p : 0 ≤ (-6:ℝ) * y 0 + (4:ℝ) * y 1 + (-2:ℝ) * y 2 := s2
        have ha : 0 ≤ ((1:ℝ)/4) * y 0 + ((1:ℝ)/2) * y 1 + ((-1:ℝ)/4) * y 2 := by linarith only [h9]
        have hb : 0 ≤ ((-3:ℝ)/4) * y 0 + ((1:ℝ)/2) * y 1 + ((-1:ℝ)/4) * y 2 := by linarith only [s2p]
        have hc : 0 ≤ ((1:ℝ)/2) * y 0 + ((-1:ℝ)/2) * y 1 + (0:ℝ) * y 2 := by linarith only [s1n]
        refine in680_close y t ht (1,1,-1) (-1,-1,-3) (0,-2,-4) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring
      · have s2n : 0 ≤ -((-6:ℝ) * y 0 + (4:ℝ) * y 1 + (-2:ℝ) * y 2) := by linarith only [s2]
        rcases le_total 0 ((-6:ℝ) * y 0 + (2:ℝ) * y 1 + (-4:ℝ) * y 2) with s3 | s3
        · have s3p : 0 ≤ (-6:ℝ) * y 0 + (2:ℝ) * y 1 + (-4:ℝ) * y 2 := s3
          have ha : 0 ≤ (0:ℝ) * y 0 + ((2:ℝ)/3) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h11]
          have hb : 0 ≤ ((-1:ℝ)/2) * y 0 + ((1:ℝ)/6) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [s3p]
          have hc : 0 ≤ ((1:ℝ)/2) * y 0 + ((-1:ℝ)/3) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [s2n]
          refine in680_close y t ht (1,1,-1) (0,-2,-4) (2,-2,-4) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
          · linarith only [hv]
          · funext i; fin_cases i <;> simp [in680vec3] <;> ring
        · have s3n : 0 ≤ -((-6:ℝ) * y 0 + (2:ℝ) * y 1 + (-4:ℝ) * y 2) := by linarith only [s3]
          have ha : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2 := by linarith only [h17]
          have hb : 0 ≤ ((-1:ℝ)/2) * y 0 + (0:ℝ) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [h20]
          have hc : 0 ≤ ((3:ℝ)/2) * y 0 + ((-1:ℝ)/2) * y 1 + (1:ℝ) * y 2 := by linarith only [s3n]
          refine in680_close y t ht (1,1,-1) (2,-2,-4) (2,0,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
          · linarith only [hv]
          · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan13 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (6:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h1 : 0 ≤ (4:ℝ) * y 0 + (6:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h2 : 0 ≤ (3:ℝ) * y 0 + (7:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h3 : 0 ≤ (3:ℝ) * y 0 + (6:ℝ) * y 1 + (0:ℝ) * y 2)
    (h4 : 0 ≤ (3:ℝ) * y 0 + (6:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h5 : 0 ≤ (2:ℝ) * y 0 + (7:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h6 : 0 ≤ (2:ℝ) * y 0 + (4:ℝ) * y 1 + (2:ℝ) * y 2)
    (h7 : 0 ≤ (1:ℝ) * y 0 + (7:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h8 : 0 ≤ (1:ℝ) * y 0 + (6:ℝ) * y 1 + (1:ℝ) * y 2)
    (h9 : 0 ≤ (1:ℝ) * y 0 + (5:ℝ) * y 1 + (2:ℝ) * y 2)
    (h10 : 0 ≤ (0:ℝ) * y 0 + (6:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h11 : 0 ≤ (0:ℝ) * y 0 + (5:ℝ) * y 1 + (2:ℝ) * y 2)
    (h12 : 0 ≤ (0:ℝ) * y 0 + (3:ℝ) * y 1 + (3:ℝ) * y 2)
    (h14 : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + (-6:ℝ) * y 2)
    (h15 : 0 ≤ (-1:ℝ) * y 0 + (6:ℝ) * y 1 + (0:ℝ) * y 2)
    (h16 : 0 ≤ (-1:ℝ) * y 0 + (6:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h17 : 0 ≤ (-1:ℝ) * y 0 + (4:ℝ) * y 1 + (2:ℝ) * y 2)
    (h18 : 0 ≤ (-2:ℝ) * y 0 + (5:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h19 : 0 ≤ (-2:ℝ) * y 0 + (4:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h20 : 0 ≤ (-3:ℝ) * y 0 + (3:ℝ) * y 1 + (0:ℝ) * y 2)
    (hv : -t ≤ (0:ℝ) * y 0 + (-6:ℝ) * y 1 + (0:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-1:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2 := s0
    have ha : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [h12]
    have hb : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h0]
    refine in680_close y t ht (0,1,0) (0,1,-1) (1,1,-1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-1:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2) := by linarith only [s0]
    have ha : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h20]
    have hb : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2 := by linarith only [h14]
    have hc : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [s0n]
    refine in680_close y t ht (0,1,0) (1,1,-1) (1,1,0) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan14 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (6:ℝ) * y 0 + (0:ℝ) * y 1 + (6:ℝ) * y 2)
    (h1 : 0 ≤ (4:ℝ) * y 0 + (6:ℝ) * y 1 + (4:ℝ) * y 2)
    (h2 : 0 ≤ (3:ℝ) * y 0 + (7:ℝ) * y 1 + (4:ℝ) * y 2)
    (h3 : 0 ≤ (3:ℝ) * y 0 + (6:ℝ) * y 1 + (6:ℝ) * y 2)
    (h4 : 0 ≤ (3:ℝ) * y 0 + (6:ℝ) * y 1 + (3:ℝ) * y 2)
    (h5 : 0 ≤ (2:ℝ) * y 0 + (7:ℝ) * y 1 + (5:ℝ) * y 2)
    (h6 : 0 ≤ (2:ℝ) * y 0 + (4:ℝ) * y 1 + (8:ℝ) * y 2)
    (h7 : 0 ≤ (1:ℝ) * y 0 + (7:ℝ) * y 1 + (5:ℝ) * y 2)
    (h8 : 0 ≤ (1:ℝ) * y 0 + (6:ℝ) * y 1 + (7:ℝ) * y 2)
    (h9 : 0 ≤ (1:ℝ) * y 0 + (5:ℝ) * y 1 + (8:ℝ) * y 2)
    (h10 : 0 ≤ (0:ℝ) * y 0 + (6:ℝ) * y 1 + (3:ℝ) * y 2)
    (h11 : 0 ≤ (0:ℝ) * y 0 + (5:ℝ) * y 1 + (8:ℝ) * y 2)
    (h12 : 0 ≤ (0:ℝ) * y 0 + (3:ℝ) * y 1 + (9:ℝ) * y 2)
    (h13 : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + (6:ℝ) * y 2)
    (h15 : 0 ≤ (-1:ℝ) * y 0 + (6:ℝ) * y 1 + (6:ℝ) * y 2)
    (h16 : 0 ≤ (-1:ℝ) * y 0 + (6:ℝ) * y 1 + (5:ℝ) * y 2)
    (h17 : 0 ≤ (-1:ℝ) * y 0 + (4:ℝ) * y 1 + (8:ℝ) * y 2)
    (h18 : 0 ≤ (-2:ℝ) * y 0 + (5:ℝ) * y 1 + (5:ℝ) * y 2)
    (h19 : 0 ≤ (-2:ℝ) * y 0 + (4:ℝ) * y 1 + (4:ℝ) * y 2)
    (h20 : 0 ≤ (-3:ℝ) * y 0 + (3:ℝ) * y 1 + (6:ℝ) * y 2)
    (hv : -t ≤ (0:ℝ) * y 0 + (-6:ℝ) * y 1 + (-6:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-1:ℝ) * y 0 + (-4:ℝ) * y 1 + (-1:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-1:ℝ) * y 0 + (-4:ℝ) * y 1 + (-1:ℝ) * y 2 := s0
    have ha : 0 ≤ ((1:ℝ)/2) * y 0 + (1:ℝ) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [h4]
    have hb : 0 ≤ ((-1:ℝ)/2) * y 0 + (-2:ℝ) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ (0:ℝ) * y 0 + (2:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [h10]
    refine in680_close y t ht (2,-1,2) (0,-1,2) (-1,0,1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-1:ℝ) * y 0 + (-4:ℝ) * y 1 + (-1:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((-2:ℝ) * y 0 + (0:ℝ) * y 1 + (2:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (-2:ℝ) * y 0 + (0:ℝ) * y 1 + (2:ℝ) * y 2 := s1
      have ha : 0 ≤ ((1:ℝ)/4) * y 0 + (0:ℝ) * y 1 + ((1:ℝ)/4) * y 2 := by linarith only [h0]
      have hb : 0 ≤ ((-1:ℝ)/2) * y 0 + (0:ℝ) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((1:ℝ)/4) * y 0 + (1:ℝ) * y 1 + ((1:ℝ)/4) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (2,-1,2) (-1,0,1) (0,1,0) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((-2:ℝ) * y 0 + (0:ℝ) * y 1 + (2:ℝ) * y 2) := by linarith only [s1]
      rcases le_total 0 ((-2:ℝ) * y 0 + (2:ℝ) * y 1 + (3:ℝ) * y 2) with s2 | s2
      · have s2p : 0 ≤ (-2:ℝ) * y 0 + (2:ℝ) * y 1 + (3:ℝ) * y 2 := s2
        have ha : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [h13]
        have hb : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + ((3:ℝ)/2) * y 2 := by linarith only [s2p]
        have hc : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2 := by linarith only [s1n]
        refine in680_close y t ht (2,-1,2) (0,1,0) (1,1,0) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring
      · have s2n : 0 ≤ -((-2:ℝ) * y 0 + (2:ℝ) * y 1 + (3:ℝ) * y 2) := by linarith only [s2]
        have ha : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (2:ℝ) * y 2 := by linarith only [h20]
        have hb : 0 ≤ (-1:ℝ) * y 0 + (2:ℝ) * y 1 + (2:ℝ) * y 2 := by linarith only [h19]
        have hc : 0 ≤ (2:ℝ) * y 0 + (-2:ℝ) * y 1 + (-3:ℝ) * y 2 := by linarith only [s2n]
        refine in680_close y t ht (2,-1,2) (1,1,0) (2,0,1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan15 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (7:ℝ) * y 0 + (-6:ℝ) * y 1 + (0:ℝ) * y 2)
    (h1 : 0 ≤ (5:ℝ) * y 0 + (0:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h2 : 0 ≤ (4:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h3 : 0 ≤ (4:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h4 : 0 ≤ (4:ℝ) * y 0 + (0:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h5 : 0 ≤ (3:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h6 : 0 ≤ (3:ℝ) * y 0 + (-2:ℝ) * y 1 + (2:ℝ) * y 2)
    (h7 : 0 ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h8 : 0 ≤ (2:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2)
    (h9 : 0 ≤ (2:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h10 : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h11 : 0 ≤ (1:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h12 : 0 ≤ (1:ℝ) * y 0 + (-3:ℝ) * y 1 + (3:ℝ) * y 2)
    (h13 : 0 ≤ (1:ℝ) * y 0 + (-6:ℝ) * y 1 + (0:ℝ) * y 2)
    (h14 : 0 ≤ (1:ℝ) * y 0 + (-6:ℝ) * y 1 + (-6:ℝ) * y 2)
    (h16 : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h17 : 0 ≤ (0:ℝ) * y 0 + (-2:ℝ) * y 1 + (2:ℝ) * y 2)
    (h18 : 0 ≤ (-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h19 : 0 ≤ (-1:ℝ) * y 0 + (-2:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h20 : 0 ≤ (-2:ℝ) * y 0 + (-3:ℝ) * y 1 + (0:ℝ) * y 2)
    (hv : -t ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((12:ℝ) * y 0 + (24:ℝ) * y 1 + (-12:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (12:ℝ) * y 0 + (24:ℝ) * y 1 + (-12:ℝ) * y 2 := s0
    have ha : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/2) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [h17]
    have hb : 0 ≤ ((1:ℝ)/2) * y 0 + (1:ℝ) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((-1:ℝ)/3) * y 0 + ((-1:ℝ)/2) * y 1 + (0:ℝ) * y 2 := by linarith only [h20]
    refine in680_close y t ht (6,-4,-2) (6,-4,-4) (6,-6,-6) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((12:ℝ) * y 0 + (24:ℝ) * y 1 + (-12:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((12:ℝ) * y 0 + (60:ℝ) * y 1 + (-84:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (12:ℝ) * y 0 + (60:ℝ) * y 1 + (-84:ℝ) * y 2 := s1
      have ha : 0 ≤ ((1:ℝ)/6) * y 0 + ((-1:ℝ)/6) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [h11]
      have hb : 0 ≤ ((1:ℝ)/18) * y 0 + ((5:ℝ)/18) * y 1 + ((-7:ℝ)/18) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((-1:ℝ)/18) * y 0 + ((-1:ℝ)/9) * y 1 + ((1:ℝ)/18) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (6,-4,-2) (6,-6,-6) (6,-18,-12) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((12:ℝ) * y 0 + (60:ℝ) * y 1 + (-84:ℝ) * y 2) := by linarith only [s1]
      rcases le_total 0 ((0:ℝ) * y 0 + (60:ℝ) * y 1 + (-120:ℝ) * y 2) with s2 | s2
      · have s2p : 0 ≤ (0:ℝ) * y 0 + (60:ℝ) * y 1 + (-120:ℝ) * y 2 := s2
        have ha : 0 ≤ ((1:ℝ)/5) * y 0 + (0:ℝ) * y 1 + ((1:ℝ)/10) * y 2 := by linarith only [h8]
        have hb : 0 ≤ (0:ℝ) * y 0 + ((1:ℝ)/6) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [s2p]
        have hc : 0 ≤ ((-1:ℝ)/30) * y 0 + ((-1:ℝ)/6) * y 1 + ((7:ℝ)/30) * y 2 := by linarith only [s1n]
        refine in680_close y t ht (6,-4,-2) (6,-18,-12) (6,-24,-12) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring
      · have s2n : 0 ≤ -((0:ℝ) * y 0 + (60:ℝ) * y 1 + (-120:ℝ) * y 2) := by linarith only [s2]
        rcases le_total 0 ((-24:ℝ) * y 0 + (-12:ℝ) * y 1 + (-48:ℝ) * y 2) with s3 | s3
        · have s3p : 0 ≤ (-24:ℝ) * y 0 + (-12:ℝ) * y 1 + (-48:ℝ) * y 2 := s3
          have ha : 0 ≤ ((1:ℝ)/5) * y 0 + ((1:ℝ)/10) * y 1 + ((-1:ℝ)/10) * y 2 := by linarith only [h7]
          have hb : 0 ≤ ((-1:ℝ)/30) * y 0 + ((-1:ℝ)/60) * y 1 + ((-1:ℝ)/15) * y 2 := by linarith only [s3p]
          have hc : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/12) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [s2n]
          refine in680_close y t ht (6,-4,-2) (6,-24,-12) (6,-12,0) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
          · linarith only [hv]
          · funext i; fin_cases i <;> simp [in680vec3] <;> ring
        · have s3n : 0 ≤ -((-24:ℝ) * y 0 + (-12:ℝ) * y 1 + (-48:ℝ) * y 2) := by linarith only [s3]
          have ha : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [h16]
          have hb : 0 ≤ ((-1:ℝ)/6) * y 0 + ((-1:ℝ)/6) * y 1 + ((-1:ℝ)/6) * y 2 := by linarith only [h18]
          have hc : 0 ≤ ((1:ℝ)/3) * y 0 + ((1:ℝ)/6) * y 1 + ((2:ℝ)/3) * y 2 := by linarith only [s3n]
          refine in680_close y t ht (6,-4,-2) (6,-12,0) (6,-6,0) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
          · linarith only [hv]
          · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan16 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (7:ℝ) * y 0 + (-6:ℝ) * y 1 + (1:ℝ) * y 2)
    (h1 : 0 ≤ (5:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h2 : 0 ≤ (4:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h3 : 0 ≤ (4:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2)
    (h4 : 0 ≤ (4:ℝ) * y 0 + (0:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h5 : 0 ≤ (3:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h6 : 0 ≤ (3:ℝ) * y 0 + (-2:ℝ) * y 1 + (3:ℝ) * y 2)
    (h7 : 0 ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h8 : 0 ≤ (2:ℝ) * y 0 + (0:ℝ) * y 1 + (2:ℝ) * y 2)
    (h9 : 0 ≤ (2:ℝ) * y 0 + (-1:ℝ) * y 1 + (3:ℝ) * y 2)
    (h10 : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h11 : 0 ≤ (1:ℝ) * y 0 + (-1:ℝ) * y 1 + (3:ℝ) * y 2)
    (h12 : 0 ≤ (1:ℝ) * y 0 + (-3:ℝ) * y 1 + (4:ℝ) * y 2)
    (h13 : 0 ≤ (1:ℝ) * y 0 + (-6:ℝ) * y 1 + (1:ℝ) * y 2)
    (h14 : 0 ≤ (1:ℝ) * y 0 + (-6:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h15 : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + (1:ℝ) * y 2)
    (h17 : 0 ≤ (0:ℝ) * y 0 + (-2:ℝ) * y 1 + (3:ℝ) * y 2)
    (h18 : 0 ≤ (-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h19 : 0 ≤ (-1:ℝ) * y 0 + (-2:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h20 : 0 ≤ (-2:ℝ) * y 0 + (-3:ℝ) * y 1 + (1:ℝ) * y 2)
    (hv : -t ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (-1:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-24:ℝ) * y 0 + (-12:ℝ) * y 1 + (24:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-24:ℝ) * y 0 + (-12:ℝ) * y 1 + (24:ℝ) * y 2 := s0
    have ha : 0 ≤ ((1:ℝ)/6) * y 0 + (0:ℝ) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h10]
    have hb : 0 ≤ ((-1:ℝ)/2) * y 0 + ((-1:ℝ)/4) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((1:ℝ)/2) * y 0 + ((1:ℝ)/4) * y 1 + (0:ℝ) * y 2 := by linarith only [h7]
    refine in680_close y t ht (6,-12,0) (4,-8,2) (4,-4,2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-24:ℝ) * y 0 + (-12:ℝ) * y 1 + (24:ℝ) * y 2) := by linarith only [s0]
    have ha : 0 ≤ ((-1:ℝ)/6) * y 0 + ((-1:ℝ)/6) * y 1 + (0:ℝ) * y 2 := by linarith only [h18]
    have hb : 0 ≤ (0:ℝ) * y 0 + (0:ℝ) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [h15]
    have hc : 0 ≤ ((1:ℝ)/3) * y 0 + ((1:ℝ)/6) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [s0n]
    refine in680_close y t ht (6,-12,0) (4,-4,2) (6,-6,0) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan17 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (7:ℝ) * y 0 + (-4:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h1 : 0 ≤ (5:ℝ) * y 0 + (2:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h2 : 0 ≤ (4:ℝ) * y 0 + (3:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h3 : 0 ≤ (4:ℝ) * y 0 + (2:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h4 : 0 ≤ (4:ℝ) * y 0 + (2:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h5 : 0 ≤ (3:ℝ) * y 0 + (3:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h6 : 0 ≤ (3:ℝ) * y 0 + (0:ℝ) * y 1 + (0:ℝ) * y 2)
    (h7 : 0 ≤ (2:ℝ) * y 0 + (3:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h8 : 0 ≤ (2:ℝ) * y 0 + (2:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h9 : 0 ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h10 : 0 ≤ (1:ℝ) * y 0 + (2:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h11 : 0 ≤ (1:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h12 : 0 ≤ (1:ℝ) * y 0 + (-1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h13 : 0 ≤ (1:ℝ) * y 0 + (-4:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h14 : 0 ≤ (1:ℝ) * y 0 + (-4:ℝ) * y 1 + (-8:ℝ) * y 2)
    (h15 : 0 ≤ (0:ℝ) * y 0 + (2:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h16 : 0 ≤ (0:ℝ) * y 0 + (2:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h18 : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h19 : 0 ≤ (-1:ℝ) * y 0 + (0:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h20 : 0 ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (hv : -t ≤ (-1:ℝ) * y 0 + (-2:ℝ) * y 1 + (2:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-12:ℝ) * y 0 + (0:ℝ) * y 1 + (-12:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-12:ℝ) * y 0 + (0:ℝ) * y 1 + (-12:ℝ) * y 2 := s0
    have ha : 0 ≤ ((1:ℝ)/2) * y 0 + ((1:ℝ)/2) * y 1 + (0:ℝ) * y 2 := by linarith only [h11]
    have hb : 0 ≤ ((-1:ℝ)/2) * y 0 + (0:ℝ) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((1:ℝ)/6) * y 0 + ((-1:ℝ)/6) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [h12]
    refine in680_close y t ht (2,0,-2) (2,-2,-4) (6,-6,-6) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-12:ℝ) * y 0 + (0:ℝ) * y 1 + (-12:ℝ) * y 2) := by linarith only [s0]
    have ha : 0 ≤ (0:ℝ) * y 0 + ((1:ℝ)/2) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [h15]
    have hb : 0 ≤ ((-1:ℝ)/3) * y 0 + ((-1:ℝ)/6) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h20]
    have hc : 0 ≤ ((1:ℝ)/2) * y 0 + (0:ℝ) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [s0n]
    refine in680_close y t ht (2,0,-2) (6,-6,-6) (6,-4,-4) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan18 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (8:ℝ) * y 0 + (-5:ℝ) * y 1 + (1:ℝ) * y 2)
    (h1 : 0 ≤ (6:ℝ) * y 0 + (1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h2 : 0 ≤ (5:ℝ) * y 0 + (2:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h3 : 0 ≤ (5:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h4 : 0 ≤ (5:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h5 : 0 ≤ (4:ℝ) * y 0 + (2:ℝ) * y 1 + (0:ℝ) * y 2)
    (h6 : 0 ≤ (4:ℝ) * y 0 + (-1:ℝ) * y 1 + (3:ℝ) * y 2)
    (h7 : 0 ≤ (3:ℝ) * y 0 + (2:ℝ) * y 1 + (0:ℝ) * y 2)
    (h8 : 0 ≤ (3:ℝ) * y 0 + (1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h9 : 0 ≤ (3:ℝ) * y 0 + (0:ℝ) * y 1 + (3:ℝ) * y 2)
    (h10 : 0 ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h11 : 0 ≤ (2:ℝ) * y 0 + (0:ℝ) * y 1 + (3:ℝ) * y 2)
    (h12 : 0 ≤ (2:ℝ) * y 0 + (-2:ℝ) * y 1 + (4:ℝ) * y 2)
    (h13 : 0 ≤ (2:ℝ) * y 0 + (-5:ℝ) * y 1 + (1:ℝ) * y 2)
    (h14 : 0 ≤ (2:ℝ) * y 0 + (-5:ℝ) * y 1 + (-5:ℝ) * y 2)
    (h15 : 0 ≤ (1:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h16 : 0 ≤ (1:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2)
    (h17 : 0 ≤ (1:ℝ) * y 0 + (-1:ℝ) * y 1 + (3:ℝ) * y 2)
    (h19 : 0 ≤ (0:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h20 : 0 ≤ (-1:ℝ) * y 0 + (-2:ℝ) * y 1 + (1:ℝ) * y 2)
    (hv : -t ≤ (-2:ℝ) * y 0 + (-1:ℝ) * y 1 + (-1:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-12:ℝ) * y 0 + (-12:ℝ) * y 1 + (6:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-12:ℝ) * y 0 + (-12:ℝ) * y 1 + (6:ℝ) * y 2 := s0
    have ha : 0 ≤ ((1:ℝ)/3) * y 0 + ((1:ℝ)/6) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h10]
    have hb : 0 ≤ (-1:ℝ) * y 0 + (-1:ℝ) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ (1:ℝ) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h16]
    refine in680_close y t ht (6,-6,0) (4,-4,2) (3,-2,2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-12:ℝ) * y 0 + (-12:ℝ) * y 1 + (6:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((-6:ℝ) * y 0 + (-6:ℝ) * y 1 + (12:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (-6:ℝ) * y 0 + (-6:ℝ) * y 1 + (12:ℝ) * y 2 := s1
      have ha : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/6) * y 1 + ((-1:ℝ)/6) * y 2 := by linarith only [h19]
      have hb : 0 ≤ ((-1:ℝ)/3) * y 0 + ((-1:ℝ)/3) * y 1 + ((2:ℝ)/3) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((2:ℝ)/3) * y 0 + ((2:ℝ)/3) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (6,-6,0) (3,-2,2) (3,-1,1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((-6:ℝ) * y 0 + (-6:ℝ) * y 1 + (12:ℝ) * y 2) := by linarith only [s1]
      have ha : 0 ≤ ((-1:ℝ)/6) * y 0 + ((-1:ℝ)/3) * y 1 + ((1:ℝ)/6) * y 2 := by linarith only [h20]
      have hb : 0 ≤ ((1:ℝ)/3) * y 0 + ((1:ℝ)/3) * y 1 + ((1:ℝ)/3) * y 2 := by linarith only [h15]
      have hc : 0 ≤ ((1:ℝ)/6) * y 0 + ((1:ℝ)/6) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [s1n]
      refine in680_close y t ht (6,-6,0) (3,-1,1) (6,-4,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan19 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (8:ℝ) * y 0 + (-4:ℝ) * y 1 + (2:ℝ) * y 2)
    (h1 : 0 ≤ (6:ℝ) * y 0 + (2:ℝ) * y 1 + (0:ℝ) * y 2)
    (h2 : 0 ≤ (5:ℝ) * y 0 + (3:ℝ) * y 1 + (0:ℝ) * y 2)
    (h3 : 0 ≤ (5:ℝ) * y 0 + (2:ℝ) * y 1 + (2:ℝ) * y 2)
    (h4 : 0 ≤ (5:ℝ) * y 0 + (2:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h5 : 0 ≤ (4:ℝ) * y 0 + (3:ℝ) * y 1 + (1:ℝ) * y 2)
    (h6 : 0 ≤ (4:ℝ) * y 0 + (0:ℝ) * y 1 + (4:ℝ) * y 2)
    (h7 : 0 ≤ (3:ℝ) * y 0 + (3:ℝ) * y 1 + (1:ℝ) * y 2)
    (h8 : 0 ≤ (3:ℝ) * y 0 + (2:ℝ) * y 1 + (3:ℝ) * y 2)
    (h9 : 0 ≤ (3:ℝ) * y 0 + (1:ℝ) * y 1 + (4:ℝ) * y 2)
    (h10 : 0 ≤ (2:ℝ) * y 0 + (2:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h11 : 0 ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (4:ℝ) * y 2)
    (h12 : 0 ≤ (2:ℝ) * y 0 + (-1:ℝ) * y 1 + (5:ℝ) * y 2)
    (h13 : 0 ≤ (2:ℝ) * y 0 + (-4:ℝ) * y 1 + (2:ℝ) * y 2)
    (h14 : 0 ≤ (2:ℝ) * y 0 + (-4:ℝ) * y 1 + (-4:ℝ) * y 2)
    (h15 : 0 ≤ (1:ℝ) * y 0 + (2:ℝ) * y 1 + (2:ℝ) * y 2)
    (h16 : 0 ≤ (1:ℝ) * y 0 + (2:ℝ) * y 1 + (1:ℝ) * y 2)
    (h17 : 0 ≤ (1:ℝ) * y 0 + (0:ℝ) * y 1 + (4:ℝ) * y 2)
    (h18 : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2)
    (h20 : 0 ≤ (-1:ℝ) * y 0 + (-1:ℝ) * y 1 + (2:ℝ) * y 2)
    (hv : -t ≤ (-2:ℝ) * y 0 + (-2:ℝ) * y 1 + (-2:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-2:ℝ) * y 0 + (1:ℝ) * y 1 + (4:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-2:ℝ) * y 0 + (1:ℝ) * y 1 + (4:ℝ) * y 2 := s0
    have ha : 0 ≤ ((1:ℝ)/3) * y 0 + ((-2:ℝ)/3) * y 1 + ((-2:ℝ)/3) * y 2 := by linarith only [h14]
    have hb : 0 ≤ ((-2:ℝ)/3) * y 0 + ((1:ℝ)/3) * y 1 + ((4:ℝ)/3) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((2:ℝ)/3) * y 0 + ((2:ℝ)/3) * y 1 + ((-1:ℝ)/3) * y 2 := by linarith only [h10]
    refine in680_close y t ht (3,-2,2) (2,-1,2) (2,0,1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-2:ℝ) * y 0 + (1:ℝ) * y 1 + (4:ℝ) * y 2) := by linarith only [s0]
    have ha : 0 ≤ ((-1:ℝ)/3) * y 0 + ((-1:ℝ)/3) * y 1 + ((2:ℝ)/3) * y 2 := by linarith only [h20]
    have hb : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [h18]
    have hc : 0 ≤ ((2:ℝ)/3) * y 0 + ((-1:ℝ)/3) * y 1 + ((-4:ℝ)/3) * y 2 := by linarith only [s0n]
    refine in680_close y t ht (3,-2,2) (2,0,1) (3,-1,1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring

theorem in680fan20 (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h0 : 0 ≤ (9:ℝ) * y 0 + (-3:ℝ) * y 1 + (0:ℝ) * y 2)
    (h1 : 0 ≤ (7:ℝ) * y 0 + (3:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h2 : 0 ≤ (6:ℝ) * y 0 + (4:ℝ) * y 1 + (-2:ℝ) * y 2)
    (h3 : 0 ≤ (6:ℝ) * y 0 + (3:ℝ) * y 1 + (0:ℝ) * y 2)
    (h4 : 0 ≤ (6:ℝ) * y 0 + (3:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h5 : 0 ≤ (5:ℝ) * y 0 + (4:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h6 : 0 ≤ (5:ℝ) * y 0 + (1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h7 : 0 ≤ (4:ℝ) * y 0 + (4:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h8 : 0 ≤ (4:ℝ) * y 0 + (3:ℝ) * y 1 + (1:ℝ) * y 2)
    (h9 : 0 ≤ (4:ℝ) * y 0 + (2:ℝ) * y 1 + (2:ℝ) * y 2)
    (h10 : 0 ≤ (3:ℝ) * y 0 + (3:ℝ) * y 1 + (-3:ℝ) * y 2)
    (h11 : 0 ≤ (3:ℝ) * y 0 + (2:ℝ) * y 1 + (2:ℝ) * y 2)
    (h12 : 0 ≤ (3:ℝ) * y 0 + (0:ℝ) * y 1 + (3:ℝ) * y 2)
    (h13 : 0 ≤ (3:ℝ) * y 0 + (-3:ℝ) * y 1 + (0:ℝ) * y 2)
    (h14 : 0 ≤ (3:ℝ) * y 0 + (-3:ℝ) * y 1 + (-6:ℝ) * y 2)
    (h15 : 0 ≤ (2:ℝ) * y 0 + (3:ℝ) * y 1 + (0:ℝ) * y 2)
    (h16 : 0 ≤ (2:ℝ) * y 0 + (3:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h17 : 0 ≤ (2:ℝ) * y 0 + (1:ℝ) * y 1 + (2:ℝ) * y 2)
    (h18 : 0 ≤ (1:ℝ) * y 0 + (2:ℝ) * y 1 + (-1:ℝ) * y 2)
    (h19 : 0 ≤ (1:ℝ) * y 0 + (1:ℝ) * y 1 + (-2:ℝ) * y 2)
    (hv : -t ≤ (-3:ℝ) * y 0 + (-3:ℝ) * y 1 + (0:ℝ) * y 2) :
    ∃ c ∈ in680W3C, y = (t / 6) • c := by
  rcases le_total 0 ((-1:ℝ) * y 0 + (1:ℝ) * y 1 + (4:ℝ) * y 2) with s0 | s0
  · have s0p : 0 ≤ (-1:ℝ) * y 0 + (1:ℝ) * y 1 + (4:ℝ) * y 2 := s0
    have ha : 0 ≤ ((1:ℝ)/2) * y 0 + ((-1:ℝ)/2) * y 1 + (-1:ℝ) * y 2 := by linarith only [h14]
    have hb : 0 ≤ ((-1:ℝ)/2) * y 0 + ((1:ℝ)/2) * y 1 + (2:ℝ) * y 2 := by linarith only [s0p]
    have hc : 0 ≤ ((1:ℝ)/2) * y 0 + ((1:ℝ)/2) * y 1 + (-1:ℝ) * y 2 := by linarith only [h19]
    refine in680_close y t ht (3,-1,1) (2,0,1) (1,1,0) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
    · linarith only [hv]
    · funext i; fin_cases i <;> simp [in680vec3] <;> ring
  · have s0n : 0 ≤ -((-1:ℝ) * y 0 + (1:ℝ) * y 1 + (4:ℝ) * y 2) := by linarith only [s0]
    rcases le_total 0 ((0:ℝ) * y 0 + (4:ℝ) * y 1 + (4:ℝ) * y 2) with s1 | s1
    · have s1p : 0 ≤ (0:ℝ) * y 0 + (4:ℝ) * y 1 + (4:ℝ) * y 2 := s1
      have ha : 0 ≤ ((1:ℝ)/4) * y 0 + ((-1:ℝ)/4) * y 1 + (0:ℝ) * y 2 := by linarith only [h13]
      have hb : 0 ≤ (0:ℝ) * y 0 + (1:ℝ) * y 1 + (1:ℝ) * y 2 := by linarith only [s1p]
      have hc : 0 ≤ ((1:ℝ)/4) * y 0 + ((-1:ℝ)/4) * y 1 + (-1:ℝ) * y 2 := by linarith only [s0n]
      refine in680_close y t ht (3,-1,1) (1,1,0) (1,1,-1) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
      · linarith only [hv]
      · funext i; fin_cases i <;> simp [in680vec3] <;> ring
    · have s1n : 0 ≤ -((0:ℝ) * y 0 + (4:ℝ) * y 1 + (4:ℝ) * y 2) := by linarith only [s1]
      rcases le_total 0 ((2:ℝ) * y 0 + (8:ℝ) * y 1 + (2:ℝ) * y 2) with s2 | s2
      · have s2p : 0 ≤ (2:ℝ) * y 0 + (8:ℝ) * y 1 + (2:ℝ) * y 2 := s2
        have ha : 0 ≤ ((1:ℝ)/4) * y 0 + (0:ℝ) * y 1 + ((1:ℝ)/4) * y 2 := by linarith only [h12]
        have hb : 0 ≤ ((1:ℝ)/4) * y 0 + (1:ℝ) * y 1 + ((1:ℝ)/4) * y 2 := by linarith only [s2p]
        have hc : 0 ≤ (0:ℝ) * y 0 + ((-1:ℝ)/2) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [s1n]
        refine in680_close y t ht (3,-1,1) (1,1,-1) (2,0,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
        · linarith only [hv]
        · funext i; fin_cases i <;> simp [in680vec3] <;> ring
      · have s2n : 0 ≤ -((2:ℝ) * y 0 + (8:ℝ) * y 1 + (2:ℝ) * y 2) := by linarith only [s2]
        rcases le_total 0 ((8:ℝ) * y 0 + (18:ℝ) * y 1 + (-6:ℝ) * y 2) with s3 | s3
        · have s3p : 0 ≤ (8:ℝ) * y 0 + (18:ℝ) * y 1 + (-6:ℝ) * y 2 := s3
          have ha : 0 ≤ ((2:ℝ)/7) * y 0 + ((1:ℝ)/7) * y 1 + ((2:ℝ)/7) * y 2 := by linarith only [h17]
          have hb : 0 ≤ ((2:ℝ)/7) * y 0 + ((9:ℝ)/14) * y 1 + ((-3:ℝ)/14) * y 2 := by linarith only [s3p]
          have hc : 0 ≤ ((-1:ℝ)/14) * y 0 + ((-2:ℝ)/7) * y 1 + ((-1:ℝ)/14) * y 2 := by linarith only [s2n]
          refine in680_close y t ht (3,-1,1) (2,0,-2) (6,-4,-4) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
          · linarith only [hv]
          · funext i; fin_cases i <;> simp [in680vec3] <;> ring
        · have s3n : 0 ≤ -((8:ℝ) * y 0 + (18:ℝ) * y 1 + (-6:ℝ) * y 2) := by linarith only [s3]
          have ha : 0 ≤ ((2:ℝ)/3) * y 0 + (1:ℝ) * y 1 + (0:ℝ) * y 2 := by linarith only [h15]
          have hb : 0 ≤ ((1:ℝ)/2) * y 0 + (1:ℝ) * y 1 + ((-1:ℝ)/2) * y 2 := by linarith only [h18]
          have hc : 0 ≤ ((-2:ℝ)/3) * y 0 + ((-3:ℝ)/2) * y 1 + ((1:ℝ)/2) * y 2 := by linarith only [s3n]
          refine in680_close y t ht (3,-1,1) (6,-4,-4) (6,-4,-2) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ _ ha hb hc ?_ ?_
          · linarith only [hv]
          · funext i; fin_cases i <;> simp [in680vec3] <;> ring
theorem in680_q3_fan (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (h : ∀ v ∈ in680V3L, -t ≤ in680dot3 v y) : ∃ c ∈ in680W3C, y = (t / 6) • c := by
  obtain ⟨v, hvm, hmin⟩ := (in680V3L.toFinset).exists_min_image (fun u => in680dot3 u y)
    ⟨(6,-6,0), by decide +kernel⟩
  have hmin' : ∀ u ∈ in680V3L, in680dot3 v y ≤ in680dot3 u y :=
    fun u hu => hmin u (List.mem_toFinset.2 hu)
  have hval : ∀ a b c : ℤ, in680dot3 (a, b, c) y = (a : ℝ) * y 0 + (b : ℝ) * y 1 + (c : ℝ) * y 2 := fun _ _ _ => rfl
  have hvmem := List.mem_toFinset.1 hvm
  have hvl := h v hvmem
  have m0 := hmin' (6,-6,0) (by decide +kernel)
  have m1 := hmin' (4,0,-2) (by decide +kernel)
  have m2 := hmin' (3,1,-2) (by decide +kernel)
  have m3 := hmin' (3,0,0) (by decide +kernel)
  have m4 := hmin' (3,0,-3) (by decide +kernel)
  have m5 := hmin' (2,1,-1) (by decide +kernel)
  have m6 := hmin' (2,-2,2) (by decide +kernel)
  have m7 := hmin' (1,1,-1) (by decide +kernel)
  have m8 := hmin' (1,0,1) (by decide +kernel)
  have m9 := hmin' (1,-1,2) (by decide +kernel)
  have m10 := hmin' (0,0,-3) (by decide +kernel)
  have m11 := hmin' (0,-1,2) (by decide +kernel)
  have m12 := hmin' (0,-3,3) (by decide +kernel)
  have m13 := hmin' (0,-6,0) (by decide +kernel)
  have m14 := hmin' (0,-6,-6) (by decide +kernel)
  have m15 := hmin' (-1,0,0) (by decide +kernel)
  have m16 := hmin' (-1,0,-1) (by decide +kernel)
  have m17 := hmin' (-1,-2,2) (by decide +kernel)
  have m18 := hmin' (-2,-1,-1) (by decide +kernel)
  have m19 := hmin' (-2,-2,-2) (by decide +kernel)
  have m20 := hmin' (-3,-3,0) (by decide +kernel)
  simp only [in680V3L, List.mem_cons, List.not_mem_nil, or_false] at hvmem
  rcases hvmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan0 y t ht (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan1 y t ht (by linarith only [m0]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan2 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan3 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan4 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan5 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan6 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan7 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan8 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan9 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan10 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan11 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan12 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan13 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan14 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan15 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan16 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan17 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan18 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m19]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan19 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m20]) (by linarith only [hvl])
  · simp only [hval] at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    push_cast at hvl m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    exact in680fan20 y t ht (by linarith only [m0]) (by linarith only [m1]) (by linarith only [m2]) (by linarith only [m3]) (by linarith only [m4]) (by linarith only [m5]) (by linarith only [m6]) (by linarith only [m7]) (by linarith only [m8]) (by linarith only [m9]) (by linarith only [m10]) (by linarith only [m11]) (by linarith only [m12]) (by linarith only [m13]) (by linarith only [m14]) (by linarith only [m15]) (by linarith only [m16]) (by linarith only [m17]) (by linarith only [m18]) (by linarith only [m19]) (by linarith only [hvl])

set_option maxHeartbeats 4000000 in
def in680expL : List (List ℤ × List ℤ) := [([6,-6,0,0,0,0,-1,-1],[1,-1,1,-1,1,1,-1,-1]),([4,0,-2,0,0,0,-1,-1],[3,1,-1,-3,-1,-1,-3,-3]),([3,1,-2,0,0,0,-1,-1],[1,3,-1,-3,1,-1,-3,-3]),([3,0,0,0,0,0,-1,-1],[3,3,3,-2,0,-1,-3,-3]),([3,0,-3,0,0,0,-1,-1],[2,2,-5,-5,-1,-2,-5,-5]),([2,1,-1,0,0,0,-1,-1],[2,8,4,-2,0,-1,-8,-8]),([2,-2,2,0,0,0,-1,-1],[3,1,5,-4,0,-2,-5,-5]),([1,1,-1,0,0,0,-1,-1],[-4,12,-2,-2,0,-1,-12,-12]),([1,0,1,0,0,0,-1,-1],[0,18,12,-2,1,-2,-18,-18]),([1,-1,2,0,0,0,-1,-1],[3,6,9,-4,0,-2,-9,-9]),([0,0,-3,0,0,0,-1,-1],[-2,3,-4,-2,0,-1,-4,-4]),([0,-1,2,0,0,0,-1,-1],[-6,12,12,-2,0,-1,-12,-12]),([0,-3,3,0,0,0,-1,-1],[0,-1,2,-2,0,-1,-2,-2]),([0,-6,0,0,0,0,-1,-1],[-1,-3,1,-3,-1,-1,-3,-3]),([0,-6,-6,0,0,0,-1,-1],[-1,-1,-1,-1,1,1,-1,-1]),([-1,0,0,0,0,0,-1,-1],[-18,18,12,-2,0,-1,-18,-18]),([-1,0,-1,0,0,0,-1,-1],[-6,8,-2,-2,0,-1,-8,-8]),([-1,-2,2,0,0,0,-1,-1],[-4,2,4,-3,1,-1,-4,-4]),([-2,-1,-1,0,0,0,-1,-1],[-5,3,-1,-2,0,-1,-5,-5]),([-2,-2,-2,0,0,0,-1,-1],[-5,1,-3,-4,0,-2,-5,-5]),([-3,-3,0,0,0,0,-1,-1],[-8,-3,2,-6,0,-3,-8,-8]),([0,0,0,6,-6,0,-1,-1],[-1,1,1,1,-1,1,-1,-1]),([0,0,0,4,0,-2,-1,-1],[-3,-1,-1,3,1,-1,-3,-3]),([0,0,0,3,1,-2,-1,-1],[-2,0,-1,1,3,-1,-3,-3]),([0,0,0,3,0,0,-1,-1],[-2,0,-1,3,3,3,-3,-3]),([0,0,0,3,0,-3,-1,-1],[-5,2,-5,2,2,-5,-5,-5]),([0,0,0,2,1,-1,-1,-1],[-2,1,-2,2,8,4,-8,-8]),([0,0,0,2,-2,2,-1,-1],[-4,0,-2,3,1,5,-5,-5]),([0,0,0,1,1,-1,-1,-1],[-3,2,-2,-4,12,-2,-12,-12]),([0,0,0,1,0,1,-1,-1],[-2,0,-1,0,18,12,-18,-18]),([0,0,0,1,-1,2,-1,-1],[-4,0,-2,3,6,9,-9,-9]),([0,0,0,0,0,-3,-1,-1],[-2,1,-2,-2,3,-4,-4,-4]),([0,0,0,0,-1,2,-1,-1],[-2,0,-1,-6,12,12,-12,-12]),([0,0,0,0,-3,3,-1,-1],[-2,0,-1,0,-1,2,-2,-2]),([0,0,0,0,-6,0,-1,-1],[-3,1,-3,-1,-3,1,-3,-3]),([0,0,0,0,-6,-6,-1,-1],[-1,1,1,-1,-1,-1,-1,-1]),([0,0,0,-1,0,0,-1,-1],[-3,2,-2,-18,18,12,-18,-18]),([0,0,0,-1,0,-1,-1,-1],[-2,1,-2,-6,8,-2,-8,-8]),([0,0,0,-1,-2,2,-1,-1],[-2,0,-1,-4,2,4,-4,-4]),([0,0,0,-2,-1,-1,-1,-1],[-2,0,-1,-5,3,-1,-5,-5]),([0,0,0,-2,-2,-2,-1,-1],[-4,0,-2,-5,1,-3,-5,-5]),([0,0,0,-3,-3,0,-1,-1],[-8,5,-6,-8,-3,2,-8,-8]),([0,0,0,0,0,0,-1,2],[0,0,0,0,0,0,-1,1]),([0,0,0,0,0,0,1,-1],[0,0,0,0,0,0,1,-1])]
noncomputable def in680ipd (w x : Fin 8 → ℝ) : ℝ := ∑ i, w i * x i

theorem in680_ipd_comb (w x y : Fin 8 → ℝ) (a b : ℝ) :
    in680ipd w (a • x + b • y) = a * in680ipd w x + b * in680ipd w y := by
  simp only [in680ipd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem in680_ipd_zero (w : Fin 8 → ℝ) : in680ipd w 0 = 0 := by simp [in680ipd]

theorem in680_facets_ncard (P : Set (Fin 8 → ℝ)) (W : Finset (Fin 8 → ℝ))
    (h0 : (0 : Fin 8 → ℝ) ∈ P) (hH : ∀ x, x ∈ P ↔ ∀ w ∈ W, -1 ≤ in680ipd w x)
    (c : (Fin 8 → ℝ) → (Fin 8 → ℝ))
    (hc : ∀ w ∈ W, c w ∈ P ∧ in680ipd w (c w) = -1 ∧ ∀ w' ∈ W, w' ≠ w → -1 < in680ipd w' (c w)) :
    (polytope_convex_facets P).ncard = W.card := by
  classical
  let F : (Fin 8 → ℝ) → Set (Fin 8 → ℝ) := fun w => {x | x ∈ P ∧ in680ipd w x = -1}
  have hle : ∀ w ∈ W, ∀ x ∈ P, -1 ≤ in680ipd w x := fun w hw x hx => (hH x).1 hx w hw
  have hFext : ∀ w ∈ W, IsExtreme ℝ P (F w) := by
    intro w hw
    refine ⟨fun x hx => hx.1, ?_⟩
    rintro x₁ hx₁ x₂ hx₂ x hx ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hx₁, ?_⟩
    have h := hx.2
    rw [in680_ipd_comb] at h
    have h1 := hle w hw _ hx₁
    have h2 := hle w hw _ hx₂
    have t1 : 0 ≤ a * (in680ipd w x₁ + 1) := mul_nonneg ha.le (by linarith)
    have t2 : 0 ≤ b * (in680ipd w x₂ + 1) := mul_nonneg hb.le (by linarith)
    have t3 : a * (in680ipd w x₁ + 1) + b * (in680ipd w x₂ + 1) = 0 := by
      have : a * in680ipd w x₁ + b * in680ipd w x₂ + (a + b) = 0 := by rw [h, hab]; ring
      linarith
    have t4 : a * (in680ipd w x₁ + 1) = 0 := by linarith
    rcases mul_eq_zero.1 t4 with h5 | h5
    · exact absurd h5 ha.ne'
    · linarith
  have hFconv : ∀ w ∈ W, Convex ℝ (F w) := by
    intro w hw x hx y hy a b ha hb hab
    refine ⟨(hH _).2 fun w' hw' => ?_, ?_⟩
    · rw [in680_ipd_comb]
      have h1 := hle w' hw' x hx.1
      have h2 := hle w' hw' y hy.1
      nlinarith
    · rw [in680_ipd_comb, hx.2, hy.2]
      nlinarith
  have hFne : ∀ w, F w ≠ P := by
    intro w he
    have : (0 : Fin 8 → ℝ) ∈ F w := he ▸ h0
    have h1 := this.2
    rw [in680_ipd_zero] at h1
    norm_num at h1
  have hcF : ∀ w ∈ W, c w ∈ F w := fun w hw => ⟨(hc w hw).1, (hc w hw).2.1⟩
  have hinj : Set.InjOn F (W : Set (Fin 8 → ℝ)) := by
    intro w hw w' hw' he
    by_contra hne
    have h1 := hcF w hw
    rw [he] at h1
    have h2 := (hc w hw).2.2 w' hw' (Ne.symm hne)
    linarith [h1.2]
  have hstrict : ∀ g, (∀ w ∈ W, -1 < in680ipd w g) → ∀ y ∈ P, ∃ y' ∈ P, g ∈ openSegment ℝ y y' := by
    intro g hg y hy
    have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ w ∈ W,
        -1 ≤ in680ipd w g + δ * (in680ipd w g - in680ipd w y) := by
      refine (Filter.eventually_all_finset W).2 fun w hw => ?_
      have hcont : Continuous fun δ : ℝ => in680ipd w g + δ * (in680ipd w g - in680ipd w y) := by
        fun_prop
      have hat : Filter.Tendsto (fun δ : ℝ => in680ipd w g + δ * (in680ipd w g - in680ipd w y))
          (nhds 0) (nhds (in680ipd w g)) := by
        simpa using hcont.tendsto 0
      have := hat.eventually (lt_mem_nhds (hg w hw))
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (this.mono fun δ h => h.le)
    obtain ⟨δ, hδ1, hδ2⟩ := (hev.and self_mem_nhdsWithin).exists
    have hδ0 : (0 : ℝ) < δ := hδ2
    refine ⟨(1 + δ) • g + (-δ) • y, (hH _).2 fun w hw => ?_, ?_⟩
    · rw [in680_ipd_comb]
      have := hδ1 w hw
      nlinarith
    · have hne : (1 + δ) ≠ 0 := by positivity
      refine ⟨δ / (1 + δ), 1 / (1 + δ), by positivity, by positivity, by field_simp; ring, ?_⟩
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  have hset : polytope_convex_facets P = F '' (W : Set (Fin 8 → ℝ)) := by
    ext G
    constructor
    · intro hG
      obtain ⟨hGext, hGconv, hGne, hGP, hGmax⟩ := hG
      have hGsub : G ⊆ P := hGext.1
      have hact : ∀ x ∈ G, ∃ w ∈ W, in680ipd w x = -1 := by
        intro x hx
        by_contra hcon
        push Not at hcon
        have hg : ∀ w ∈ W, -1 < in680ipd w x := fun w hw =>
          lt_of_le_of_ne (hle w hw x (hGsub hx)) (hcon w hw).symm
        apply hGP
        refine Set.Subset.antisymm hGsub fun y hy => ?_
        obtain ⟨y', hy', hseg⟩ := hstrict x hg y hy
        exact hGext.2 hy hy' hx hseg
      let A : (Fin 8 → ℝ) → Finset (Fin 8 → ℝ) := fun x => W.filter (fun w => in680ipd w x = -1)
      obtain ⟨x0, hx0, hx0min⟩ : ∃ x0 ∈ G, ∀ x ∈ G, (A x0).card ≤ (A x).card := by
        let S : Set ℕ := {n | ∃ x ∈ G, (A x).card = n}
        have hSne : S.Nonempty := by
          obtain ⟨x, hx⟩ := hGne
          exact ⟨_, x, hx, rfl⟩
        obtain ⟨x0, hx0, hc0⟩ := Nat.sInf_mem hSne
        refine ⟨x0, hx0, fun x hx => ?_⟩
        rw [hc0]
        exact Nat.sInf_le ⟨x, hx, rfl⟩
      obtain ⟨w0, hw0, hw0a⟩ := hact x0 hx0
      have hsub : G ⊆ F w0 := by
        intro z hz
        have hm : (1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • z ∈ G :=
          hGconv hx0 hz (by norm_num) (by norm_num) (by norm_num)
        have hAsub : A ((1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • z) ⊆ A x0 := by
          intro w hw
          obtain ⟨hwW, hwe⟩ := Finset.mem_filter.1 hw
          rw [in680_ipd_comb] at hwe
          have h1 := hle w hwW _ (hGsub hx0)
          have h2 := hle w hwW _ (hGsub hz)
          exact Finset.mem_filter.2 ⟨hwW, by linarith⟩
        have hAeq : A ((1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • z) = A x0 :=
          Finset.eq_of_subset_of_card_le hAsub (hx0min _ hm)
        have hw0m : w0 ∈ A ((1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • z) := by
          rw [hAeq]
          exact Finset.mem_filter.2 ⟨hw0, hw0a⟩
        obtain ⟨_, hwe⟩ := Finset.mem_filter.1 hw0m
        rw [in680_ipd_comb] at hwe
        have h1 := hle w0 hw0 _ (hGsub hx0)
        have h2 := hle w0 hw0 _ (hGsub hz)
        exact ⟨hGsub hz, by linarith⟩
      rcases hGmax _ (hFext w0 hw0) (hFconv w0 hw0) hsub with h | h
      · exact ⟨w0, hw0, h⟩
      · exact absurd h (hFne w0)
    · rintro ⟨w, hw, rfl⟩
      refine ⟨hFext w hw, hFconv w hw, ⟨c w, hcF w hw⟩, hFne w, ?_⟩
      intro G hGext hGconv hsub
      by_cases heq : G = F w
      · exact Or.inl heq
      · right
        obtain ⟨x, hxG, hxF⟩ : ∃ x ∈ G, x ∉ F w := by
          by_contra hcon
          push Not at hcon
          exact heq (Set.Subset.antisymm hcon hsub)
        have hGP : G ⊆ P := hGext.1
        have hxstrict : -1 < in680ipd w x := by
          refine lt_of_le_of_ne (hle w hw x (hGP hxG)) ?_
          intro h
          exact hxF ⟨hGP hxG, h.symm⟩
        have hcw := hc w hw
        have hg : (1 / 2 : ℝ) • c w + (1 / 2 : ℝ) • x ∈ G :=
          hGconv (hsub (hcF w hw)) hxG (by norm_num) (by norm_num) (by norm_num)
        have hgstrict : ∀ w' ∈ W, -1 < in680ipd w' ((1 / 2 : ℝ) • c w + (1 / 2 : ℝ) • x) := by
          intro w' hw'
          rw [in680_ipd_comb]
          by_cases hww : w' = w
          · subst hww
            rw [hcw.2.1]
            linarith
          · have h1 := hcw.2.2 w' hw' hww
            have h2 := hle w' hw' x (hGP hxG)
            linarith
        refine Set.Subset.antisymm hGP fun y hy => ?_
        obtain ⟨y', hy', hseg⟩ := hstrict _ hgstrict y hy
        exact hGext.2 hy hy' hg hseg
  rw [hset, Set.ncard_image_of_injOn hinj, Set.ncard_coe_finset]

def in680rv (z : Fin 8 → ℤ) : Fin 8 → ℝ := fun i => (z i : ℝ)
def in680dot8 (z z' : Fin 8 → ℤ) : ℤ := ∑ i, z i * z' i
def in680lift (a b : ℤ × ℤ × ℤ) : Fin 8 → ℤ := ![a.1, a.2.1, a.2.2, b.1, b.2.1, b.2.2, -3, -2]
def in680e7 : Fin 8 → ℤ := ![0, 0, 0, 0, 0, 0, 1, 0]
def in680e8 : Fin 8 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 1]
def in680l1 (q : ℤ × ℤ × ℤ) : Fin 8 → ℤ := ![q.1, q.2.1, q.2.2, 0, 0, 0, -1, -1]
def in680l2 (q : ℤ × ℤ × ℤ) : Fin 8 → ℤ := ![0, 0, 0, q.1, q.2.1, q.2.2, -1, -1]
def in680ap1 : Fin 8 → ℤ := ![0, 0, 0, 0, 0, 0, -1, 2]
def in680ap2 : Fin 8 → ℤ := ![0, 0, 0, 0, 0, 0, 1, -1]
def in680dot3Z (a q : ℤ × ℤ × ℤ) : ℤ := a.1 * q.1 + a.2.1 * q.2.1 + a.2.2 * q.2.2
def in680V8L : List (Fin 8 → ℤ) := in680V3L.map in680l1 ++ in680V3L.map in680l2 ++ [in680ap1, in680ap2]

theorem in680_ipd_rv (z z' : Fin 8 → ℤ) :
    in680ipd (in680rv z) (in680rv z') = (in680dot8 z z' : ℝ) := by
  simp [in680ipd, in680rv, in680dot8]

theorem in680_lb : ∀ a ∈ in680W3L, ∀ q ∈ in680V3L, -6 ≤ in680dot3Z a q := by decide +kernel
theorem in680_tight : ∀ a ∈ in680W3L, ∃ q ∈ in680V3L, in680dot3Z a q = -6 := by decide +kernel
theorem in680_slack : ∀ a ∈ in680W3L, ∃ q ∈ in680V3L, -6 < in680dot3Z a q := by decide +kernel
theorem in680_sep : ∀ a ∈ in680W3L, ∀ b ∈ in680W3L, a ≠ b →
    ∃ q ∈ in680V3L, in680dot3Z a q = -6 ∧ -6 < in680dot3Z b q := by decide +kernel
theorem in680_W3_nodup : in680W3L.Nodup := by decide +kernel
theorem in680_W3_len : in680W3L.length = 37 := by decide +kernel
theorem in680_V8_sub : ∀ z ∈ in680V8L, z ∈ p8_vertices := by decide +kernel
theorem in680_V8_sup : ∀ z ∈ p8_vertices, z ∈ in680V8L := by decide +kernel
theorem in680_V8_card : p8_vertices.card = 44 := by decide +kernel
def in680vl (l : List ℤ) : Fin 8 → ℤ := fun i => l.getD i.val 0
theorem in680_exp1 : ∀ p ∈ in680expL, ∀ z ∈ in680V8L, z ≠ in680vl p.1 →
    in680dot8 (in680vl p.2) z < in680dot8 (in680vl p.2) (in680vl p.1) := by
  decide +kernel
theorem in680_exp2 : ∀ z ∈ p8_vertices, ∃ p ∈ in680expL, in680vl p.1 = z := by decide +kernel

theorem in680_dot_lift_l1 (a b q : ℤ × ℤ × ℤ) :
    in680dot8 (in680lift a b) (in680l1 q) = in680dot3Z a q + 5 := by
  simp [in680dot8, Fin.sum_univ_eight, in680lift, in680l1, in680dot3Z]; ring
theorem in680_dot_lift_l2 (a b q : ℤ × ℤ × ℤ) :
    in680dot8 (in680lift a b) (in680l2 q) = in680dot3Z b q + 5 := by
  simp [in680dot8, Fin.sum_univ_eight, in680lift, in680l2, in680dot3Z]; ring
theorem in680_dot_lift_ap1 (a b : ℤ × ℤ × ℤ) : in680dot8 (in680lift a b) in680ap1 = -1 := by
  simp [in680dot8, Fin.sum_univ_eight, in680lift, in680ap1]
theorem in680_dot_lift_ap2 (a b : ℤ × ℤ × ℤ) : in680dot8 (in680lift a b) in680ap2 = -1 := by
  simp [in680dot8, Fin.sum_univ_eight, in680lift, in680ap2]
theorem in680_dot_e7 (q : ℤ × ℤ × ℤ) :
    in680dot8 in680e7 (in680l1 q) = -1 ∧ in680dot8 in680e7 (in680l2 q) = -1 ∧
    in680dot8 in680e7 in680ap1 = -1 ∧ in680dot8 in680e7 in680ap2 = 1 := by
  simp [in680dot8, Fin.sum_univ_eight, in680e7, in680l1, in680l2, in680ap1, in680ap2]
theorem in680_dot_e8 (q : ℤ × ℤ × ℤ) :
    in680dot8 in680e8 (in680l1 q) = -1 ∧ in680dot8 in680e8 (in680l2 q) = -1 ∧
    in680dot8 in680e8 in680ap1 = 2 ∧ in680dot8 in680e8 in680ap2 = -1 := by
  simp [in680dot8, Fin.sum_univ_eight, in680e8, in680l1, in680l2, in680ap1, in680ap2]

noncomputable def in680W8 : Finset (Fin 8 → ℤ) :=
  ((in680W3L.toFinset ×ˢ in680W3L.toFinset).image (fun p => in680lift p.1 p.2)) ∪ {in680e7, in680e8}

theorem in680_W8_cases {w : Fin 8 → ℤ} (hw : w ∈ in680W8) :
    (∃ a ∈ in680W3L, ∃ b ∈ in680W3L, w = in680lift a b) ∨ w = in680e7 ∨ w = in680e8 := by
  simp only [in680W8, Finset.mem_union, Finset.mem_image, Finset.mem_product, List.mem_toFinset,
    Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with ⟨⟨a, b⟩, ⟨h1, h2⟩, rfl⟩ | h | h
  · exact Or.inl ⟨a, h1, b, h2, rfl⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem in680_lift_mem {a b : ℤ × ℤ × ℤ} (ha : a ∈ in680W3L) (hb : b ∈ in680W3L) :
    in680lift a b ∈ in680W8 := by
  simp only [in680W8, Finset.mem_union, Finset.mem_image, Finset.mem_product, List.mem_toFinset]
  exact Or.inl ⟨(a, b), ⟨ha, hb⟩, rfl⟩

theorem in680_e7_mem : in680e7 ∈ in680W8 := by simp [in680W8]
theorem in680_e8_mem : in680e8 ∈ in680W8 := by simp [in680W8]

theorem in680_V8_cases {z : Fin 8 → ℤ} (hz : z ∈ p8_vertices) :
    (∃ q ∈ in680V3L, z = in680l1 q) ∨ (∃ q ∈ in680V3L, z = in680l2 q) ∨ z = in680ap1 ∨ z = in680ap2 := by
  have h := in680_V8_sup z hz
  simp only [in680V8L, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | h | h
  · exact Or.inl ⟨q, hq, rfl⟩
  · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem in680_W8_V8 : ∀ w ∈ in680W8, ∀ z ∈ p8_vertices, -1 ≤ in680dot8 w z := by
  intro w hw z hz
  rcases in680_W8_cases hw with ⟨a, ha, b, hb, rfl⟩ | rfl | rfl <;>
    rcases in680_V8_cases hz with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | rfl | rfl
  · rw [in680_dot_lift_l1]; have := in680_lb a ha q hq; omega
  · rw [in680_dot_lift_l2]; have := in680_lb b hb q hq; omega
  · rw [in680_dot_lift_ap1]
  · rw [in680_dot_lift_ap2]
  · rw [(in680_dot_e7 q).1]
  · rw [(in680_dot_e7 q).2.1]
  · rw [(in680_dot_e7 (0, 0, 0)).2.2.1]
  · rw [(in680_dot_e7 (0, 0, 0)).2.2.2]; norm_num
  · rw [(in680_dot_e8 q).1]
  · rw [(in680_dot_e8 q).2.1]
  · rw [(in680_dot_e8 (0, 0, 0)).2.2.1]; norm_num
  · rw [(in680_dot_e8 (0, 0, 0)).2.2.2]

abbrev in680P : Set (Fin 8 → ℝ) := p8_polytope

theorem in680_P_eq : in680P = convexHull ℝ (in680rv '' (p8_vertices : Set (Fin 8 → ℤ))) := rfl

theorem in680_P_conv : Convex ℝ in680P := convex_convexHull _ _

theorem in680_vert_mem {z : Fin 8 → ℤ} (hz : z ∈ p8_vertices) : in680rv z ∈ in680P :=
  subset_convexHull _ _ ⟨z, hz, rfl⟩

theorem in680_halfspace_conv (w : Fin 8 → ℝ) : Convex ℝ {x : Fin 8 → ℝ | -1 ≤ in680ipd w x} := by
  intro x hx y hy a b ha hb hab
  show -1 ≤ in680ipd w (a • x + b • y)
  rw [in680_ipd_comb]
  have h1 : -1 ≤ in680ipd w x := hx
  have h2 : -1 ≤ in680ipd w y := hy
  nlinarith

theorem in680_P_sub_halfspace {w : Fin 8 → ℤ} (hw : w ∈ in680W8) :
    ∀ x ∈ in680P, -1 ≤ in680ipd (in680rv w) x := by
  intro x hx
  have hmin : convexHull ℝ (in680rv '' (p8_vertices : Set (Fin 8 → ℤ))) ⊆
      {x : Fin 8 → ℝ | -1 ≤ in680ipd (in680rv w) x} := by
    refine convexHull_min ?_ (in680_halfspace_conv _)
    rintro _ ⟨z, hz, rfl⟩
    show -1 ≤ in680ipd (in680rv w) (in680rv z)
    rw [in680_ipd_rv]
    have := in680_W8_V8 w hw z hz
    exact_mod_cast this
  exact hmin hx

theorem in680_W8_halfspace {x : Fin 8 → ℝ} (h : ∀ w ∈ in680W8, -1 ≤ in680ipd (in680rv w) x) :
    ∀ y ∈ convexHull ℝ (in680rv '' (in680W8 : Set (Fin 8 → ℤ))), -1 ≤ in680ipd y x := by
  intro y hy
  have hconv : Convex ℝ {y : Fin 8 → ℝ | -1 ≤ in680ipd y x} := by
    intro p hp q hq a b ha hb hab
    show -1 ≤ in680ipd (a • p + b • q) x
    have e : in680ipd (a • p + b • q) x = a * in680ipd p x + b * in680ipd q x := by
      simp only [in680ipd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    have h1 : -1 ≤ in680ipd p x := hp
    have h2 : -1 ≤ in680ipd q x := hq
    nlinarith
  have hmin : convexHull ℝ (in680rv '' (in680W8 : Set (Fin 8 → ℤ))) ⊆ {y | -1 ≤ in680ipd y x} := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  exact hmin hy

theorem in680_ipd_comb_left (p q x : Fin 8 → ℝ) (a b : ℝ) :
    in680ipd (a • p + b • q) x = a * in680ipd p x + b * in680ipd q x := by
  simp only [in680ipd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem in680_l1_vert {q : ℤ × ℤ × ℤ} (hq : q ∈ in680V3L) : in680l1 q ∈ p8_vertices :=
  in680_V8_sub _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨q, hq, rfl⟩)))))
theorem in680_l2_vert {q : ℤ × ℤ × ℤ} (hq : q ∈ in680V3L) : in680l2 q ∈ p8_vertices :=
  in680_V8_sub _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨q, hq, rfl⟩)))))
theorem in680_ap1_vert : in680ap1 ∈ p8_vertices := in680_V8_sub _ (by simp [in680V8L])
theorem in680_ap2_vert : in680ap2 ∈ p8_vertices := in680_V8_sub _ (by simp [in680V8L])

theorem in680_ipd_l1 (q : ℤ × ℤ × ℤ) (y : Fin 8 → ℝ) :
    in680ipd (in680rv (in680l1 q)) y = (q.1 : ℝ) * y 0 + (q.2.1 : ℝ) * y 1 + (q.2.2 : ℝ) * y 2 - y 6 - y 7 := by
  simp [in680ipd, Fin.sum_univ_eight, in680rv, in680l1]; ring
theorem in680_ipd_l2 (q : ℤ × ℤ × ℤ) (y : Fin 8 → ℝ) :
    in680ipd (in680rv (in680l2 q)) y = (q.1 : ℝ) * y 3 + (q.2.1 : ℝ) * y 4 + (q.2.2 : ℝ) * y 5 - y 6 - y 7 := by
  simp [in680ipd, Fin.sum_univ_eight, in680rv, in680l2]; ring
theorem in680_ipd_ap1 (y : Fin 8 → ℝ) : in680ipd (in680rv in680ap1) y = -y 6 + 2 * y 7 := by
  simp [in680ipd, Fin.sum_univ_eight, in680rv, in680ap1]
theorem in680_ipd_ap2 (y : Fin 8 → ℝ) : in680ipd (in680rv in680ap2) y = y 6 - y 7 := by
  simp [in680ipd, Fin.sum_univ_eight, in680rv, in680ap2]; ring

noncomputable def in680gg (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : Fin 8 → ℝ :=
  ![p.1 0, p.1 1, p.1 2, p.2 0, p.2 1, p.2 2, -3, -2]

def in680C : Set (Fin 8 → ℝ) := convexHull ℝ (in680rv '' (in680W8 : Set (Fin 8 → ℤ)))

theorem in680_C_conv : Convex ℝ in680C := convex_convexHull _ _

theorem in680_W8_mem_C {w : Fin 8 → ℤ} (hw : w ∈ in680W8) : in680rv w ∈ in680C :=
  subset_convexHull _ _ ⟨w, hw, rfl⟩

theorem in680_prod_mem {ca cb : Fin 3 → ℝ} (hca : ca ∈ in680W3C) (hcb : cb ∈ in680W3C) :
    in680gg (ca, cb) ∈ in680C := by
  let A : Set (Fin 3 → ℝ) := in680vec3 '' {t | t ∈ in680W3L}
  have hmem : (ca, cb) ∈ convexHull ℝ (A ×ˢ A) := by
    rw [convexHull_prod]
    exact ⟨hca, hcb⟩
  have hDconv : Convex ℝ {p : (Fin 3 → ℝ) × (Fin 3 → ℝ) | in680gg p ∈ in680C} := by
    intro p hp q hq a b ha hb hab
    show in680gg (a • p + b • q) ∈ in680C
    have e : in680gg (a • p + b • q) = a • in680gg p + b • in680gg q := by
      funext i
      fin_cases i <;> simp [in680gg] <;> linarith
    rw [e]
    exact in680_C_conv hp hq ha hb hab
  have hsub : A ×ˢ A ⊆ {p | in680gg p ∈ in680C} := by
    rintro ⟨u, v⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    show in680gg (in680vec3 a, in680vec3 b) ∈ in680C
    have e : in680gg (in680vec3 a, in680vec3 b) = in680rv (in680lift a b) := by
      funext i
      fin_cases i <;> simp [in680gg, in680vec3, in680rv, in680lift]
    rw [e]
    exact in680_W8_mem_C (in680_lift_mem ha hb)
  exact convexHull_min hsub hDconv hmem

theorem in680_conv3 {C : Set (Fin 8 → ℝ)} (hC : Convex ℝ C) {p q r : Fin 8 → ℝ}
    (hp : p ∈ C) (hq : q ∈ C) (hr : r ∈ C) {l1 l2 l3 : ℝ}
    (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (h3 : 0 ≤ l3) (hs : l1 + l2 + l3 = 1) :
    l1 • p + l2 • q + l3 • r ∈ C := by
  have := hC.sum_mem (t := Finset.univ) (w := ![l1, l2, l3]) (z := ![p, q, r])
    (by intro i _; fin_cases i <;> simp [h1, h2, h3])
    (by simp [Fin.sum_univ_succ]; linarith)
    (by intro i _; fin_cases i <;> simp [hp, hq, hr])
  simpa [Fin.sum_univ_succ, add_assoc] using this

theorem in680_polar_sub (y : Fin 8 → ℝ)
    (hy : ∀ z ∈ p8_vertices, -1 ≤ in680ipd (in680rv z) y) : y ∈ in680C := by
  set τ : ℝ := 1 - y 6 - y 7 with hτ
  have hq1 : ∀ q ∈ in680V3L, -τ ≤ (q.1 : ℝ) * y 0 + (q.2.1 : ℝ) * y 1 + (q.2.2 : ℝ) * y 2 := by
    intro q hq
    have := hy _ (in680_l1_vert hq)
    rw [in680_ipd_l1] at this
    rw [hτ]; linarith
  have hq2 : ∀ q ∈ in680V3L, -τ ≤ (q.1 : ℝ) * y 3 + (q.2.1 : ℝ) * y 4 + (q.2.2 : ℝ) * y 5 := by
    intro q hq
    have := hy _ (in680_l2_vert hq)
    rw [in680_ipd_l2] at this
    rw [hτ]; linarith
  have ha1 := hy _ in680_ap1_vert
  have ha2 := hy _ in680_ap2_vert
  rw [in680_ipd_ap1] at ha1
  rw [in680_ipd_ap2] at ha2
  have hτ0 : 0 ≤ τ := by
    have t1 := hq1 (6, -6, 0) (by decide +kernel)
    have t2 := hq1 (3, 1, -2) (by decide +kernel)
    have t3 := hq1 (1, 0, 1) (by decide +kernel)
    have t4 := hq1 (-1, 0, 0) (by decide +kernel)
    norm_num at t1 t2 t3 t4
    linarith only [t1, t2, t3, t4]
  obtain ⟨ca, hca, ea⟩ := in680_q3_fan ![y 0, y 1, y 2] τ hτ0 (fun v hv => by
    have := hq1 v hv
    simpa [in680dot3] using this)
  obtain ⟨cb, hcb, eb⟩ := in680_q3_fan ![y 3, y 4, y 5] τ hτ0 (fun v hv => by
    have := hq2 v hv
    simpa [in680dot3] using this)
  have e0 : y 0 = τ / 6 * ca 0 := by simpa using congrFun ea 0
  have e1 : y 1 = τ / 6 * ca 1 := by simpa using congrFun ea 1
  have e2 : y 2 = τ / 6 * ca 2 := by simpa using congrFun ea 2
  have e3 : y 3 = τ / 6 * cb 0 := by simpa using congrFun eb 0
  have e4 : y 4 = τ / 6 * cb 1 := by simpa using congrFun eb 1
  have e5 : y 5 = τ / 6 * cb 2 := by simpa using congrFun eb 2
  have hmem := in680_conv3 in680_C_conv (in680_W8_mem_C in680_e7_mem) (in680_W8_mem_C in680_e8_mem)
    (in680_prod_mem hca hcb) (l1 := y 6 + τ / 2) (l2 := y 7 + τ / 3) (l3 := τ / 6)
    (by rw [hτ]; linarith) (by rw [hτ]; linarith) (by positivity) (by rw [hτ]; ring)
  convert hmem using 1
  funext i
  fin_cases i <;> simp [in680gg, in680rv, in680e7, in680e8] <;> linarith [e0, e1, e2, e3, e4, e5]

theorem in680_polar_eq : polytope_polar in680P = in680C := by
  apply Set.Subset.antisymm
  · intro y hy
    refine in680_polar_sub y fun z hz => ?_
    exact hy (in680rv z) (in680_vert_mem hz)
  · intro y hy
    show ∀ x ∈ in680P, -1 ≤ ∑ i, x i * y i
    intro x hx
    have hconv : Convex ℝ {x : Fin 8 → ℝ | -1 ≤ in680ipd x y} := by
      intro p hp q hq a b ha hb hab
      show -1 ≤ in680ipd (a • p + b • q) y
      rw [in680_ipd_comb_left]
      have h1 : -1 ≤ in680ipd p y := hp
      have h2 : -1 ≤ in680ipd q y := hq
      nlinarith
    have hsub : in680rv '' (p8_vertices : Set (Fin 8 → ℤ)) ⊆ {x : Fin 8 → ℝ | -1 ≤ in680ipd x y} := by
      rintro _ ⟨z, hz, rfl⟩
      show -1 ≤ in680ipd (in680rv z) y
      have h := in680_W8_halfspace (x := in680rv z) (fun w hw => ?_) y hy
      · exact (show in680ipd (in680rv z) y = in680ipd y (in680rv z) by
          simp only [in680ipd]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _).symm ▸ h
      · rw [in680_ipd_rv]
        have := in680_W8_V8 w hw z hz
        exact_mod_cast this
    exact convexHull_min hsub hconv hx

theorem in680_zero_P : (0 : Fin 8 → ℝ) ∈ in680P := by
  have hc := in680_P_conv
  have h1 := in680_vert_mem (in680_l1_vert (q := (6, -6, 0)) (by decide +kernel))
  have h2 := in680_vert_mem (in680_l1_vert (q := (3, 1, -2)) (by decide +kernel))
  have h3 := in680_vert_mem (in680_l1_vert (q := (1, 0, 1)) (by decide +kernel))
  have h4 := in680_vert_mem (in680_l1_vert (q := (-1, 0, 0)) (by decide +kernel))
  have h5 := in680_vert_mem in680_ap1_vert
  have h6 := in680_vert_mem in680_ap2_vert
  have hm := hc.sum_mem (t := Finset.univ) (w := ![1/330, 1/55, 2/55, 6/55, 1/3, 1/2])
    (z := ![in680rv (in680l1 (6, -6, 0)), in680rv (in680l1 (3, 1, -2)), in680rv (in680l1 (1, 0, 1)),
      in680rv (in680l1 (-1, 0, 0)), in680rv in680ap1, in680rv in680ap2])
    (by intro i _; fin_cases i <;> simp <;> norm_num)
    (by simp [Fin.sum_univ_succ]; norm_num)
    (by intro i _; fin_cases i <;> simp [h1, h2, h3, h4, h5, h6])
  convert hm using 1
  funext j
  fin_cases j <;> simp [Fin.sum_univ_succ, in680rv, in680l1, in680ap1, in680ap2] <;> norm_num

theorem in680_H (x : Fin 8 → ℝ) : x ∈ in680P ↔ ∀ w ∈ in680W8, -1 ≤ in680ipd (in680rv w) x := by
  constructor
  · exact fun hx w hw => in680_P_sub_halfspace hw x hx
  · intro h
    by_contra hx
    have hcomp : IsCompact in680P :=
      Set.Finite.isCompact_convexHull ℝ (Set.Finite.image _ (Finset.finite_toSet _))
    obtain ⟨f, u, hf1, hf2⟩ := geometric_hahn_banach_closed_point in680_P_conv hcomp.isClosed hx
    have hu : 0 < u := by
      have := hf1 0 in680_zero_P
      simpa using this
    have hbasis : ∀ v : Fin 8 → ℝ, f v = ∑ i, v i * f (fun j => if i = j then 1 else 0) := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ v]
      simp [map_sum]
    set y : Fin 8 → ℝ := fun i => -(f (fun j => if i = j then 1 else 0)) / u with hydef
    have hyip : ∀ v : Fin 8 → ℝ, in680ipd v y = -(f v) / u := by
      intro v
      rw [hbasis v]
      simp only [in680ipd, hydef, Finset.sum_div, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hyC : y ∈ in680C := by
      rw [← in680_polar_eq]
      intro p hp
      show -1 ≤ in680ipd p y
      rw [hyip, neg_div, neg_le_neg_iff, div_le_one hu]
      exact (hf1 p hp).le
    have h1 := in680_W8_halfspace h y hyC
    have h2 : in680ipd y x = in680ipd x y := by
      simp only [in680ipd]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h2, hyip, neg_div] at h1
    have h3 : 1 < f x / u := (one_lt_div hu).2 hf2
    linarith

theorem in680_interior : (0 : Fin 8 → ℝ) ∈ interior in680P := by
  have hopen : IsOpen (⋂ w ∈ in680W8, {x : Fin 8 → ℝ | -1 < in680ipd (in680rv w) x}) := by
    refine isOpen_biInter_finset fun w _ => ?_
    exact isOpen_lt continuous_const (by unfold in680ipd; fun_prop)
  have hsub : (⋂ w ∈ in680W8, {x : Fin 8 → ℝ | -1 < in680ipd (in680rv w) x}) ⊆ in680P := by
    intro x hx
    rw [in680_H]
    intro w hw
    exact le_of_lt (Set.mem_iInter₂.1 hx w hw)
  refine interior_maximal hsub hopen ?_
  refine Set.mem_iInter₂.2 fun w _ => ?_
  show -1 < in680ipd (in680rv w) 0
  rw [in680_ipd_zero]
  norm_num

theorem in680_rv_inj : Function.Injective in680rv := by
  intro z z' h
  funext i
  have := congrFun h i
  simpa [in680rv] using this

theorem in680_cvx_le {α β A B c : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (h1 : A ≤ c) (h2 : B ≤ c) : α * A + β * B ≤ c := by
  have e : α * c + β * c = c := by rw [← add_mul, hαβ, one_mul]
  linarith [mul_le_mul_of_nonneg_left h1 hα, mul_le_mul_of_nonneg_left h2 hβ]

theorem in680_cvx_lt {α β A B c : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (h1 : A < c) (h2 : B < c) : α * A + β * B < c := by
  rcases eq_or_lt_of_le hα with h0 | h0
  · have : β = 1 := by rw [← h0] at hαβ; linarith
    rw [← h0, this]
    linarith
  · have e : α * c + β * c = c := by rw [← add_mul, hαβ, one_mul]
    linarith [mul_lt_mul_of_pos_left h1 h0, mul_le_mul_of_nonneg_left h2.le hβ]

theorem in680_ipd_sum (u : Fin 8 → ℝ) {ι : Type*} (S : Finset ι) (β : ι → ℝ) (f : ι → Fin 8 → ℝ) :
    in680ipd u (∑ z ∈ S, β z • f z) = ∑ z ∈ S, β z * in680ipd u (f z) := by
  simp only [in680ipd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem in680_extreme : (Set.extremePoints ℝ in680P).ncard = 44 := by
  classical
  have hS : Set.extremePoints ℝ in680P = in680rv '' (p8_vertices : Set (Fin 8 → ℤ)) := by
    apply Set.Subset.antisymm
    · exact extremePoints_convexHull_subset
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨p, hp, hpe⟩ := in680_exp2 z hz
      set u : Fin 8 → ℤ := in680vl p.2 with hu
      have hstrict : ∀ z' ∈ p8_vertices, z' ≠ z → in680dot8 u z' < in680dot8 u z := by
        intro z' hz' hne
        have := in680_exp1 p hp z' (in680_V8_sup z' hz') (by rw [hpe]; exact hne)
        rwa [hpe] at this
      set c : ℝ := in680ipd (in680rv u) (in680rv z) with hc
      have hle : ∀ x ∈ in680P, in680ipd (in680rv u) x ≤ c := by
        intro x hx
        have hconv : Convex ℝ {x : Fin 8 → ℝ | in680ipd (in680rv u) x ≤ c} := by
          intro a ha b hb α β hα hβ hαβ
          show in680ipd (in680rv u) (α • a + β • b) ≤ c
          rw [in680_ipd_comb]
          have h1 : in680ipd (in680rv u) a ≤ c := ha
          have h2 : in680ipd (in680rv u) b ≤ c := hb
          exact in680_cvx_le hα hβ hαβ h1 h2
        refine (convexHull_min ?_ hconv) hx
        rintro _ ⟨z', hz', rfl⟩
        show in680ipd (in680rv u) (in680rv z') ≤ c
        rw [hc, in680_ipd_rv, in680_ipd_rv]
        by_cases hne : z' = z
        · rw [hne]
        · exact_mod_cast (hstrict z' hz' hne).le
      have huniq : ∀ x ∈ in680P, in680ipd (in680rv u) x = c → x = in680rv z := by
        intro x hx hxc
        set S' : Set (Fin 8 → ℝ) := in680rv '' (p8_vertices : Set (Fin 8 → ℤ)) \ {in680rv z} with hS'
        have hSins : in680rv '' (p8_vertices : Set (Fin 8 → ℤ)) = insert (in680rv z) S' := by
          rw [hS']
          rw [Set.insert_diff_singleton, Set.insert_eq_of_mem (Set.mem_image_of_mem in680rv hz)]
        have hS'ne : S'.Nonempty := by
          by_cases hc1 : z = in680ap1
          · refine ⟨in680rv in680ap2, ⟨in680ap2, in680_ap2_vert, rfl⟩, ?_⟩
            intro h
            have h' := in680_rv_inj (Set.mem_singleton_iff.1 h)
            rw [hc1] at h'
            exact absurd h' (by decide +kernel)
          · refine ⟨in680rv in680ap1, ⟨in680ap1, in680_ap1_vert, rfl⟩, ?_⟩
            intro h
            exact hc1 (in680_rv_inj (Set.mem_singleton_iff.1 h)).symm
        have hT : ∀ b ∈ convexHull ℝ S', in680ipd (in680rv u) b < c := by
          intro b hb
          have hconv : Convex ℝ {x : Fin 8 → ℝ | in680ipd (in680rv u) x < c} := by
            intro a ha b' hb' α β hα hβ hαβ
            show in680ipd (in680rv u) (α • a + β • b') < c
            rw [in680_ipd_comb]
            have h1 : in680ipd (in680rv u) a < c := ha
            have h2 : in680ipd (in680rv u) b' < c := hb'
            exact in680_cvx_lt hα hβ hαβ h1 h2
          refine (convexHull_min ?_ hconv) hb
          rintro _ ⟨⟨z', hz', rfl⟩, hne⟩
          show in680ipd (in680rv u) (in680rv z') < c
          rw [hc, in680_ipd_rv, in680_ipd_rv]
          have hne' : z' ≠ z := fun e => hne (e ▸ rfl)
          exact_mod_cast hstrict z' hz' hne'
        have hx' : x ∈ convexHull ℝ (insert (in680rv z) S') := by rw [← hSins]; exact hx
        rw [convexHull_insert hS'ne] at hx'
        obtain ⟨a, ha, b, hb, hxseg⟩ := mem_convexJoin.1 hx'
        obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hxseg
        have ha' : a = in680rv z := Set.mem_singleton_iff.1 ha
        subst ha'
        rw [in680_ipd_comb] at hxc
        have hbc := hT b hb
        have h1 : β * (c - in680ipd (in680rv u) b) = 0 := by
          linear_combination c * hαβ - hxc
        have hne : c - in680ipd (in680rv u) b ≠ 0 := by
          intro h
          linarith
        have hβ0 : β = 0 := (mul_eq_zero.1 h1).resolve_right hne
        have hα1 : α = 1 := by rw [hβ0] at hαβ; linarith
        rw [hα1, hβ0]
        simp
      refine mem_extremePoints_iff_left.2 ⟨in680_vert_mem hz, ?_⟩
      intro x₁ hx₁ x₂ hx₂ hseg
      obtain ⟨α, β, hα, hβ, hαβ, heq⟩ := hseg
      have h1 := hle x₁ hx₁
      have h2 := hle x₂ hx₂
      have h3 : α * in680ipd (in680rv u) x₁ + β * in680ipd (in680rv u) x₂ = c := by
        rw [← in680_ipd_comb, heq]
      have h4 : α * (c - in680ipd (in680rv u) x₁) = 0 := by
        have a1 : 0 ≤ α * (c - in680ipd (in680rv u) x₁) := mul_nonneg hα.le (sub_nonneg.2 h1)
        have a2 : 0 ≤ β * (c - in680ipd (in680rv u) x₂) := mul_nonneg hβ.le (sub_nonneg.2 h2)
        have a3 : α * (c - in680ipd (in680rv u) x₁) + β * (c - in680ipd (in680rv u) x₂) = 0 := by
          linear_combination c * hαβ - h3
        linarith
      have hne : α ≠ 0 := hα.ne'
      have h5 : in680ipd (in680rv u) x₁ = c := by
        have := (mul_eq_zero.1 h4).resolve_left hne
        linarith
      exact huniq x₁ hx₁ h5
  rw [hS, Set.ncard_image_of_injective _ in680_rv_inj, Set.ncard_coe_finset, in680_V8_card]

theorem in680_W8_card : in680W8.card = 1371 := by
  classical
  have hdis : Disjoint ((in680W3L.toFinset ×ˢ in680W3L.toFinset).image (fun p => in680lift p.1 p.2))
      ({in680e7, in680e8} : Finset (Fin 8 → ℤ)) := by
    rw [Finset.disjoint_left]
    rintro x hx hy
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h
    · have := congrFun h 6
      simp [in680lift, in680e7] at this
    · have := congrFun h 6
      simp [in680lift, in680e8] at this
  have hinj : Function.Injective (fun p : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) => in680lift p.1 p.2) := by
    rintro ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩ ⟨⟨c0, c1, c2⟩, ⟨d0, d1, d2⟩⟩ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    have h5 := congrFun h 5
    simp only [in680lift, Matrix.cons_val] at h0 h1 h2 h3 h4 h5
    simp_all
  have htf : in680W3L.toFinset.card = 37 := by
    rw [List.toFinset_card_of_nodup in680_W3_nodup, in680_W3_len]
  have hne : in680e7 ≠ in680e8 := by decide +kernel
  rw [in680W8, Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ hinj,
    Finset.card_product, htf, Finset.card_pair hne]

theorem in680_sep_ints {w w' : Fin 8 → ℤ} (hw : w ∈ in680W8) (hw' : w' ∈ in680W8) (hne : w ≠ w') :
    ∃ z ∈ p8_vertices, in680dot8 w z = -1 ∧ -1 < in680dot8 w' z := by
  rcases in680_W8_cases hw with ⟨a, ha, b, hb, rfl⟩ | rfl | rfl <;>
    rcases in680_W8_cases hw' with ⟨a', ha', b', hb', rfl⟩ | rfl | rfl
  · by_cases heq : a = a'
    · have hbb : b ≠ b' := fun e => hne (by rw [heq, e])
      obtain ⟨q, hq, h1, h2⟩ := in680_sep b hb b' hb' hbb
      refine ⟨in680l2 q, in680_l2_vert hq, ?_, ?_⟩
      · rw [in680_dot_lift_l2]; omega
      · rw [in680_dot_lift_l2]; omega
    · obtain ⟨q, hq, h1, h2⟩ := in680_sep a ha a' ha' heq
      refine ⟨in680l1 q, in680_l1_vert hq, ?_, ?_⟩
      · rw [in680_dot_lift_l1]; omega
      · rw [in680_dot_lift_l1]; omega
  · refine ⟨in680ap2, in680_ap2_vert, in680_dot_lift_ap2 a b, ?_⟩
    rw [(in680_dot_e7 (0, 0, 0)).2.2.2]; norm_num
  · refine ⟨in680ap1, in680_ap1_vert, in680_dot_lift_ap1 a b, ?_⟩
    rw [(in680_dot_e8 (0, 0, 0)).2.2.1]; norm_num
  · obtain ⟨q, hq, h1⟩ := in680_slack a' ha'
    refine ⟨in680l1 q, in680_l1_vert hq, (in680_dot_e7 q).1, ?_⟩
    rw [in680_dot_lift_l1]; omega
  · exact absurd rfl hne
  · exact ⟨in680ap1, in680_ap1_vert, (in680_dot_e7 (0, 0, 0)).2.2.1, by
      rw [(in680_dot_e8 (0, 0, 0)).2.2.1]; norm_num⟩
  · obtain ⟨q, hq, h1⟩ := in680_slack a' ha'
    refine ⟨in680l1 q, in680_l1_vert hq, (in680_dot_e8 q).1, ?_⟩
    rw [in680_dot_lift_l1]; omega
  · exact ⟨in680ap2, in680_ap2_vert, (in680_dot_e8 (0, 0, 0)).2.2.2, by
      rw [(in680_dot_e7 (0, 0, 0)).2.2.2]; norm_num⟩
  · exact absurd rfl hne

theorem in680_tight_W {w : Fin 8 → ℤ} (hw : w ∈ in680W8) : ∃ z ∈ p8_vertices, in680dot8 w z = -1 := by
  rcases in680_W8_cases hw with ⟨a, ha, b, hb, rfl⟩ | rfl | rfl
  · obtain ⟨q, hq, h1⟩ := in680_tight a ha
    exact ⟨in680l1 q, in680_l1_vert hq, by rw [in680_dot_lift_l1]; omega⟩
  · exact ⟨in680ap1, in680_ap1_vert, (in680_dot_e7 (0, 0, 0)).2.2.1⟩
  · exact ⟨in680ap2, in680_ap2_vert, (in680_dot_e8 (0, 0, 0)).2.2.2⟩

theorem in680_centroid {w : Fin 8 → ℤ} (hw : w ∈ in680W8) :
    ∃ c ∈ in680P, in680ipd (in680rv w) c = -1 ∧
      ∀ w' ∈ in680W8, w' ≠ w → -1 < in680ipd (in680rv w') c := by
  classical
  set VW := p8_vertices.filter (fun z => in680dot8 w z = -1) with hVW
  have hne : VW.Nonempty := by
    obtain ⟨z, hz, h⟩ := in680_tight_W hw
    exact ⟨z, Finset.mem_filter.2 ⟨hz, h⟩⟩
  set k : ℝ := (VW.card : ℝ) with hk
  have hk0 : 0 < k := by
    rw [hk]
    exact_mod_cast Finset.card_pos.2 hne
  have hsum : ∑ _z ∈ VW, (1 / k) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ← hk]
    field_simp
  refine ⟨∑ z ∈ VW, (1 / k) • in680rv z, ?_, ?_, ?_⟩
  · refine in680_P_conv.sum_mem (fun _ _ => (one_div_pos.2 hk0).le) hsum (fun z hz => ?_)
    exact in680_vert_mem (Finset.mem_filter.1 hz).1
  · rw [in680_ipd_sum]
    have : ∑ z ∈ VW, (1 / k) * in680ipd (in680rv w) (in680rv z) = ∑ z ∈ VW, (1 / k) * (-1) := by
      refine Finset.sum_congr rfl fun z hz => ?_
      rw [in680_ipd_rv, (Finset.mem_filter.1 hz).2]
      norm_num
    rw [this, ← Finset.sum_mul, hsum]
    norm_num
  · intro w' hw' hne'
    rw [in680_ipd_sum]
    obtain ⟨z1, hz1, h1, h2⟩ := in680_sep_ints hw hw' (Ne.symm hne')
    have hz1W : z1 ∈ VW := Finset.mem_filter.2 ⟨hz1, h1⟩
    have hlower : ∀ z ∈ VW, -1 ≤ in680ipd (in680rv w') (in680rv z) := by
      intro z hz
      rw [in680_ipd_rv]
      exact_mod_cast in680_W8_V8 w' hw' z (Finset.mem_filter.1 hz).1
    have hstrict : -1 < in680ipd (in680rv w') (in680rv z1) := by
      rw [in680_ipd_rv]
      exact_mod_cast h2
    have hpos : 0 < ∑ z ∈ VW, (1 / k) * (in680ipd (in680rv w') (in680rv z) + 1) := by
      refine Finset.sum_pos' (fun z hz => ?_) ⟨z1, hz1W, ?_⟩
      · have := hlower z hz
        have hk1 : 0 < 1 / k := one_div_pos.2 hk0
        exact mul_nonneg hk1.le (by linarith)
      · have hk1 : 0 < 1 / k := one_div_pos.2 hk0
        exact mul_pos hk1 (by linarith)
    have hexp : ∑ z ∈ VW, (1 / k) * (in680ipd (in680rv w') (in680rv z) + 1)
        = ∑ z ∈ VW, (1 / k) * in680ipd (in680rv w') (in680rv z) + 1 := by
      simp only [mul_add, Finset.sum_add_distrib, mul_one, hsum]
    linarith

theorem p8_reflexive_with_1371_convex_facets :
    is_reflexive_polytope p8_polytope ∧
    (Set.extremePoints ℝ p8_polytope).ncard = 44 ∧
    (polytope_convex_facets p8_polytope).ncard = 1371 ∧
    (polytope_convex_facets p8_polytope).ncard > 6 ^ (8 / 2) := by
  classical
  have hfac : (polytope_convex_facets in680P).ncard = 1371 := by
    let W : Finset (Fin 8 → ℝ) := in680W8.image in680rv
    have hmemW : ∀ y, y ∈ W ↔ ∃ w ∈ in680W8, in680rv w = y := by
      intro y
      simp only [W, Finset.mem_image]
    have hH' : ∀ x, x ∈ in680P ↔ ∀ w ∈ W, -1 ≤ in680ipd w x := by
      intro x
      rw [in680_H]
      constructor
      · intro h w hw
        obtain ⟨w0, hw0, rfl⟩ := (hmemW w).1 hw
        exact h w0 hw0
      · intro h w hw
        exact h _ ((hmemW _).2 ⟨w, hw, rfl⟩)
    have hcent : ∀ w ∈ W, ∃ c, c ∈ in680P ∧ in680ipd w c = -1 ∧
        ∀ w' ∈ W, w' ≠ w → -1 < in680ipd w' c := by
      intro w hw
      obtain ⟨w0, hw0, rfl⟩ := (hmemW w).1 hw
      obtain ⟨c, h1, h2, h3⟩ := in680_centroid hw0
      refine ⟨c, h1, h2, fun w' hw' hne => ?_⟩
      obtain ⟨w1, hw1, rfl⟩ := (hmemW w').1 hw'
      exact h3 w1 hw1 (fun e => hne (by rw [e]))
    choose! c hc using hcent
    have h := in680_facets_ncard in680P W in680_zero_P hH' c hc
    rw [h, Finset.card_image_of_injective _ in680_rv_inj, in680_W8_card]
  refine ⟨⟨⟨p8_vertices, rfl⟩, in680_interior, ⟨in680W8, in680_polar_eq⟩⟩, in680_extreme, hfac, ?_⟩
  rw [hfac]
  norm_num
