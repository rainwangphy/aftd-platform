import AFTD.Prelude
import AFTD.Kb.Tcs.GoodSlopesProductDenseRowLevelLines

/-!
# good_slopes_colored_dense_row_levels_axis

Topic: combinatorics   Node: 96a8ef0ebdee

Provenance: helper lemma. Axis-line reduction for the colored product argument in OP-1027.

For a colored pq-point subset of a product of finite-field planes, any q-point level in a dense nonzero first-field row projects to a vertical or horizontal line in the second-field plane, provided r<q and equal colors cannot collide in a pair of nonzero forms.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_colored_dense_row_levels_axis
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (p q r : ℕ) (hp : Fintype.card K = p) (hq : Fintype.card L = q) (hrq : r < q)
    (hdirL : ∀ T : Finset (L × L), T.card = q →
      (∃ G : Finset L, (q+1)/2 ≤ G.card ∧ ∀ b ∈ G, Set.InjOn (fun z : L × L => z.2 + b*z.1) T) →
      (∃ x : L, ∀ z ∈ T, z.1 = x) ∨ (∃ b t : L, ∀ z ∈ T, z.2 + b*z.1 = t))
    (S : Finset ((K × L) × (K × L))) (color : ((K × L) × (K × L)) → Fin r)
    (hcard : S.card = p*q)
    (hc : ∀ a : K, a ≠ 0 → ∀ b : L, b ≠ 0 → ∀ u ∈ S, ∀ v ∈ S, color u = color v →
      (u.2.1 + a*u.1.1, u.2.2 + b*u.1.2) = (v.2.1 + a*v.1.1, v.2.2 + b*v.1.2) → u = v)
    (a : K) (ha : a ≠ 0)
    (hdense : (q+1)/2 ≤ ((Finset.univ : Finset L).filter fun b => b ≠ 0 ∧
      Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S).card) :
    ∀ t : K, (S.filter fun z => z.2.1 + a*z.1.1 = t).card = q ∧
      ((∃ x : L, ∀ z ∈ S, z.2.1 + a*z.1.1 = t → z.1.2 = x) ∨
       (∃ y : L, ∀ z ∈ S, z.2.1 + a*z.1.1 = t → z.2.2 = y)) := by
  classical
  intro t
  have hl := good_slopes_product_dense_row_level_lines K L p q hp hq hdirL S hcard a hdense t
  refine ⟨hl.1, ?_⟩
  rcases hl.2 with hv | ⟨b,y,hy⟩
  · exact Or.inl hv
  · by_cases hb : b = 0
    · right
      refine ⟨y, ?_⟩
      intro z hz ht
      simpa [hb] using hy z hz ht
    · let A := S.filter fun z => z.2.1 + a*z.1.1 = t
      have hcol : Set.InjOn color A := by
        intro u hu v hv he
        have hu' := Finset.mem_filter.mp hu
        have hv' := Finset.mem_filter.mp hv
        apply hc a ha b hb u hu'.1 v hv'.1 he
        apply Prod.ext
        · exact hu'.2.trans hv'.2.symm
        · exact (hy u hu'.1 hu'.2).trans (hy v hv'.1 hv'.2).symm
      have hle : A.card ≤ r := by
        calc
          A.card = (A.image color).card := (Finset.card_image_of_injOn hcol).symm
          _ ≤ Fintype.card (Fin r) := Finset.card_le_univ _
          _ = r := Fintype.card_fin r
      have hA : A.card = q := hl.1
      omega
