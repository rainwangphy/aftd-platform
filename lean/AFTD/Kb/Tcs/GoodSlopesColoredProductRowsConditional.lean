import AFTD.Prelude
import AFTD.Kb.Tcs.GoodSlopesColoredProductTwoDenseRowsConditional
import AFTD.Kb.Tcs.GoodSlopesColoredProductFullRowsAllConditional

/-!
# good_slopes_colored_product_rows_conditional

Topic: combinatorics   Node: 9c80bb7f8365

Provenance: helper lemma. General product-fiber row rigidity reduction for OP-1027; prime direction hypotheses compare arXiv:2611.04551 Lemma 2.7.

For fields of cardinalities p<q and r colors with r<p and (p+1)r<2q, assume the two finite-field direction classification bounds. If at least max(2,(p+1)/2) nonzero p-coordinate rows each have at least (q+1)/2 good nonzero q-coordinate slopes, then every unit-coordinate direction is good.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
private theorem in962_dense_to_full {K : Type*} [Fintype K] [DecidableEq K]
    (D F : Finset K) (h2 : 2 ≤ D.card)
    (hstep : ∀ a ∈ D, ∀ a' ∈ D, a ≠ a' → a ∈ F) : D ⊆ F := by
  intro a ha
  have herase : 0 < (D.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨a', ha'⟩ := Finset.card_pos.mp herase
  have ha'm := Finset.mem_erase.mp ha'
  exact hstep a ha a' ha'm.2 (Ne.symm ha'm.1)

theorem good_slopes_colored_product_rows_conditional
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (p q r : ℕ) (hp : Fintype.card K = p) (hq : Fintype.card L = q)
    (hrp : r < p) (hpq : p < q) (hsize : (p+1)*r < 2*q)
    (hdirK : ∀ T : Finset (K × K), T.card = p →
      (∃ G : Finset K, (p+1)/2 ≤ G.card ∧ ∀ a ∈ G, Set.InjOn (fun z : K × K => z.2 + a*z.1) T) →
      (∃ x : K, ∀ z ∈ T, z.1 = x) ∨ (∃ a t : K, ∀ z ∈ T, z.2 + a*z.1 = t))
    (hdirL : ∀ T : Finset (L × L), T.card = q →
      (∃ G : Finset L, (q+1)/2 ≤ G.card ∧ ∀ b ∈ G, Set.InjOn (fun z : L × L => z.2 + b*z.1) T) →
      (∃ x : L, ∀ z ∈ T, z.1 = x) ∨ (∃ b t : L, ∀ z ∈ T, z.2 + b*z.1 = t))
    (S : Finset ((K × L) × (K × L))) (color : ((K × L) × (K × L)) → Fin r)
    (hcard : S.card = p*q)
    (hx : ∀ u ∈ S, ∀ v ∈ S, color u = color v → u.1 = v.1 → u = v)
    (hc : ∀ a : K, a ≠ 0 → ∀ b : L, b ≠ 0 → ∀ u ∈ S, ∀ v ∈ S, color u = color v →
      (u.2.1 + a*u.1.1, u.2.2 + b*u.1.2) = (v.2.1 + a*v.1.1, v.2.2 + b*v.1.2) → u = v)
    (hrows : max 2 ((p+1)/2) ≤ ((Finset.univ : Finset K).filter fun a => a ≠ 0 ∧
      (q+1)/2 ≤ ((Finset.univ : Finset L).filter fun b => b ≠ 0 ∧
        Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S).card).card) :
    ∀ a : K, a ≠ 0 → ∀ b : L, b ≠ 0 →
      Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S := by
  classical
  let D : Finset K := Finset.univ.filter fun a => a ≠ 0 ∧
    (q+1)/2 ≤ ((Finset.univ : Finset L).filter fun b => b ≠ 0 ∧
      Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1+a*z.1.1,z.2.2+b*z.1.2)) S).card
  let U : Finset K := Finset.univ.filter fun a => a ≠ 0 ∧ ∀ b : L, b ≠ 0 →
    Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1+a*z.1.1,z.2.2+b*z.1.2)) S
  have h2 : 2 ≤ D.card := le_trans (le_max_left _ _) hrows
  have ht : (p+1)/2 ≤ D.card := le_trans (le_max_right _ _) hrows
  have hsub : D ⊆ U := by
    apply in962_dense_to_full D U h2
    intro a ha a' ha' hne
    have hda := (Finset.mem_filter.mp ha).2
    have hda' := (Finset.mem_filter.mp ha').2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hda.1, ?_⟩
    exact good_slopes_colored_product_two_dense_rows_conditional K L p q r hp hq hrp hpq hsize
      hdirL S color hcard hx hc a a' hda.1 hda'.1 hne hda.2 hda'.2
  have hfull : (p+1)/2 ≤ U.card := le_trans ht (Finset.card_le_card hsub)
  exact good_slopes_colored_product_full_rows_all_conditional K L p q r hp hq hrp hdirK S color hcard hc hfull
