import AFTD.Prelude
import AFTD.Kb.Tcs.GoodSlopesFiberProductSaturation
import AFTD.Kb.Tcs.GoodSlopesFiniteRowsNoVertical
import AFTD.Kb.Tcs.GoodSlopesProductDenseRowLevelLines
import AFTD.Kb.Tcs.GoodSlopesColoredDenseRowLevelsAxis
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# good_slopes_colored_product_two_dense_rows_conditional

Topic: combinatorics   Node: 93e878803bca

Provenance: helper lemma. Dense rows become full in the colored product step for OP-1027.

For a colored pq-point set over finite fields satisfying the stated size and same-color injectivity conditions, if two distinct nonzero rows each contain at least (q+1)/2 good nonzero second-field directions, then the first row is entirely good.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_colored_product_two_dense_rows_conditional
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (p q r : ℕ) (hp : Fintype.card K = p) (hq : Fintype.card L = q)
    (hrp : r < p) (hpq : p < q) (hsize : (p+1)*r < 2*q)
    (hdirL : ∀ T : Finset (L × L), T.card = q →
      (∃ G : Finset L, (q+1)/2 ≤ G.card ∧ ∀ b ∈ G, Set.InjOn (fun z : L × L => z.2 + b*z.1) T) →
      (∃ x : L, ∀ z ∈ T, z.1 = x) ∨ (∃ b t : L, ∀ z ∈ T, z.2 + b*z.1 = t))
    (S : Finset ((K × L) × (K × L))) (color : ((K × L) × (K × L)) → Fin r)
    (hcard : S.card = p*q)
    (hx : ∀ u ∈ S, ∀ v ∈ S, color u = color v → u.1 = v.1 → u = v)
    (hc : ∀ a : K, a ≠ 0 → ∀ b : L, b ≠ 0 → ∀ u ∈ S, ∀ v ∈ S, color u = color v →
      (u.2.1 + a*u.1.1, u.2.2 + b*u.1.2) = (v.2.1 + a*v.1.1, v.2.2 + b*v.1.2) → u = v)
    (a a' : K) (ha : a ≠ 0) (ha' : a' ≠ 0) (hne : a ≠ a')
    (hdense : (q+1)/2 ≤ ((Finset.univ : Finset L).filter fun b => b ≠ 0 ∧
      Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S).card)
    (hdense' : (q+1)/2 ≤ ((Finset.univ : Finset L).filter fun b => b ≠ 0 ∧
      Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a'*z.1.1, z.2.2 + b*z.1.2)) S).card) :
    ∀ b : L, b ≠ 0 → Set.InjOn (fun z : ((K × L) × (K × L)) =>
      (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S := by
  classical
  let F (z : ((K × L) × (K × L))) := z.2.1+a*z.1.1
  let E (z : ((K × L) × (K × L))) := z.2.1+a'*z.1.1
  let X (z : ((K × L) × (K × L))) := z.1.2
  have hqpos : 1 < q := by rw [← hq]; exact Fintype.one_lt_card
  have hrq : r < q := by omega
  have hgap : p+r ≤ q := by
    by_cases hr : r ≤ 1
    · omega
    · have hr2 : 2 ≤ r := by omega
      have hp1 : 1 ≤ p := by omega
      have hm := Nat.mul_le_mul_right (p-1) hr2
      have hpr : (p-1)+1 = p := by omega
      have hright : (p+1)*r = r*(p-1)+2*r := by
        calc
          (p+1)*r = ((p-1)+1+1)*r := by rw [hpr]
          _ = r*(p-1)+2*r := by ring
      have hleft : 2*(p+r-1) = 2*(p-1)+2*r := by omega
      have hn : 2*(p+r-1) ≤ (p+1)*r := by omega
      omega
  have hsize' : r*p < 2*q := by nlinarith
  have hA := good_slopes_colored_dense_row_levels_axis K L p q r hp hq hrq hdirL S color hcard hc a ha hdense
  have hB := good_slopes_colored_dense_row_levels_axis K L p q r hp hq hrq hdirL S color hcard hc a' ha' hdense'
  let G (a0 : K) : Finset L := Finset.univ.filter fun b => b ≠ 0 ∧
    Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1+a0*z.1.1,z.2.2+b*z.1.2)) S
  have hGpos : ∀ a0, (q+1)/2 ≤ (G a0).card → 0 < (G a0).card := by
    intro a0 hg; omega
  have hdA : (q+1)/2 ≤ (G a).card := hdense
  have hdB : (q+1)/2 ≤ (G a').card := hdense'
  obtain ⟨b0,hb0⟩ := Finset.card_pos.mp (hGpos a hdA)
  obtain ⟨b1,hb1⟩ := Finset.card_pos.mp (hGpos a' hdB)
  have hb0good := (Finset.mem_filter.mp hb0).2.2
  have hb1good := (Finset.mem_filter.mp hb1).2.2
  have hrows : ∀ t, (S.filter fun z => F z = t).card = q := fun t => (hA t).1
  have hcols : ∀ t, (S.filter fun z => E z = t).card = q := fun t => (hB t).1
  have hbound : ∀ k, (S.filter fun z => X z = k).card ≤ r*p := by
    intro k
    let T := S.filter fun z => X z = k
    let φ (z : ((K × L) × (K × L))) := (z.1.1,color z)
    have hφ : Set.InjOn φ T := by
      intro u hu v hv he
      have hu' := Finset.mem_filter.mp hu
      have hv' := Finset.mem_filter.mp hv
      have hK := congrArg Prod.fst he
      have hC := congrArg Prod.snd he
      apply hx u hu'.1 v hv'.1 hC
      exact Prod.ext hK (hu'.2.trans hv'.2.symm)
    have hle : T.card ≤ Fintype.card (K × Fin r) := by
      calc
        _ = (T.image φ).card := (Finset.card_image_of_injOn hφ).symm
        _ ≤ _ := Finset.card_le_univ _
    simpa [Fintype.card_prod, hp, Nat.mul_comm] using hle
  have hcross : ∀ i j k, (S.filter fun z => F z = i ∧ E z = j ∧ X z = k).card ≤ r := by
    intro i j k
    let T := S.filter fun z => F z = i ∧ E z = j ∧ X z = k
    have hcol : Set.InjOn color T := by
      intro u hu v hv hcuv
      have hu' := Finset.mem_filter.mp hu
      have hv' := Finset.mem_filter.mp hv
      have h1 : u.2.1+a*u.1.1 = v.2.1+a*v.1.1 := hu'.2.1.trans hv'.2.1.symm
      have h2 : u.2.1+a'*u.1.1 = v.2.1+a'*v.1.1 := hu'.2.2.1.trans hv'.2.2.1.symm
      have hm : (a-a')*(u.1.1-v.1.1)=0 := by linear_combination h1-h2
      have hK : u.1.1 = v.1.1 := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hne))
      apply hx u hu'.1 v hv'.1 hcuv
      exact Prod.ext hK (hu'.2.2.2.trans hv'.2.2.2.symm)
    have hle : T.card ≤ Fintype.card (Fin r) := by
      calc
        _ = (T.image color).card := (Finset.card_image_of_injOn hcol).symm
        _ ≤ _ := Finset.card_le_univ _
    simpa using hle
  have hclass : ∀ j, (∃ k, ∀ z ∈ S, E z = j → X z = k) ∨
      Set.InjOn X {z | z ∈ S ∧ E z = j} := by
    intro j
    rcases (hB j).2 with hv | ⟨y,hy⟩
    · exact Or.inl hv
    · right
      intro u hu v hv he
      apply hb1good hu.1 hv.1
      apply Prod.ext
      · exact hu.2.trans hv.2.symm
      · have huY := hy u hu.1 hu.2
        have hvY := hy v hv.1 hv.2
        dsimp [X] at he
        change u.2.2+b1*u.1.2 = v.2.2+b1*v.1.2
        rw [he, huY.trans hvY.symm]
  have hnotv := good_slopes_finite_rows_no_vertical S F E X p q r hp hsize' hgap hrows hcols hbound hcross hclass
  intro b hb u hu v hv heq
  have hK := congrArg Prod.fst heq
  have hL := congrArg Prod.snd heq
  let t := F u
  rcases (hA t).2 with ⟨x,hxv⟩ | ⟨y,hy⟩
  · exact False.elim (hnotv t x hxv)
  · have huY := hy u hu rfl
    have hvY := hy v hv hK.symm
    have hY : u.2.2 = v.2.2 := huY.trans hvY.symm
    have hX : u.1.2 = v.1.2 := by
      apply (mul_left_inj' hb).mp
      linear_combination hL-hY
    apply hb0good hu hv
    apply Prod.ext
    · exact hK
    · change u.2.2+b0*u.1.2 = v.2.2+b0*v.1.2
      rw [hX,hY]
