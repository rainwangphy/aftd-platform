import AFTD.Prelude
import AFTD.Kb.Tcs.GoodSlopesFiberProductSaturation
import AFTD.Kb.Tcs.GoodSlopesProductDenseRowLevelLines

/-!
# good_slopes_product_dense_row_bad_column_conditional

Topic: combinatorics   Node: 1aa272d7b45e

Provenance: helper lemma. One dense row forces a bad column in OP-1027.

Over finite fields with p<q, if a nonzero row has at least (q+1)/2 good nonzero directions and one bad nonzero direction, then every nonzero row is bad in that same column, assuming the q-point direction classification.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_product_dense_row_bad_column_conditional
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (p q : ℕ) (hp : Fintype.card K = p) (hq : Fintype.card L = q) (hpq : p < q)
    (hdirL : ∀ T : Finset (L × L), T.card = q →
      (∃ G : Finset L, (q+1)/2 ≤ G.card ∧ ∀ b ∈ G, Set.InjOn (fun z : L × L => z.2 + b*z.1) T) →
      (∃ x : L, ∀ z ∈ T, z.1 = x) ∨ (∃ b t : L, ∀ z ∈ T, z.2 + b*z.1 = t))
    (S : Finset ((K × L) × (K × L))) (hcard : S.card = p*q)
    (a : K) (ha : a ≠ 0)
    (hdense : (q+1)/2 ≤ ((Finset.univ : Finset L).filter fun b => b ≠ 0 ∧
      Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S).card)
    (b : L) (hb : b ≠ 0)
    (hbad : ¬ Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S) :
    ∀ a' : K, a' ≠ 0 → ¬ Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a'*z.1.1, z.2.2 + b*z.1.2)) S := by
  classical
  obtain ⟨u,hu,v,hv,heq,hne⟩ : ∃ u ∈ S, ∃ v ∈ S,
      (u.2.1+a*u.1.1,u.2.2+b*u.1.2) = (v.2.1+a*v.1.1,v.2.2+b*v.1.2) ∧ u ≠ v := by
    simp only [Set.InjOn, not_forall] at hbad
    obtain ⟨u,hu,v,hv,he,hne⟩ := hbad
    exact ⟨u,hu,v,hv,he,hne⟩
  have hK := congrArg Prod.fst heq
  have hL := congrArg Prod.snd heq
  change u.2.1+a*u.1.1 = v.2.1+a*v.1.1 at hK
  change u.2.2+b*u.1.2 = v.2.2+b*v.1.2 at hL
  let G : Finset L := Finset.univ.filter fun c => c ≠ 0 ∧
      Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1+a*z.1.1,z.2.2+c*z.1.2)) S
  have hqpos : 1 < q := by rw [←hq]; exact Fintype.one_lt_card
  have hn : 0 < (q+1)/2 := Nat.div_pos (by omega) (by decide)
  have hGpos : 0 < G.card := lt_of_lt_of_le hn hdense
  obtain ⟨c,hc⟩ := Finset.card_pos.mp hGpos
  have hgood := (Finset.mem_filter.mp hc).2.2
  have hdx : u.1.2 ≠ v.1.2 := by
    intro hx
    have hy : u.2.2 = v.2.2 := by linear_combination hL - b*hx
    apply hne
    apply hgood hu hv
    apply Prod.ext
    · exact hK
    · change u.2.2+c*u.1.2 = v.2.2+c*v.1.2
      rw [hx,hy]
  let t : K := u.2.1+a*u.1.1
  let Q := S.filter fun z => z.2.1+a*z.1.1=t
  have huQ : u ∈ Q := Finset.mem_filter.mpr ⟨hu,rfl⟩
  have hvQ : v ∈ Q := Finset.mem_filter.mpr ⟨hv,hK.symm⟩
  have hl := good_slopes_product_dense_row_level_lines K L p q hp hq hdirL S hcard a hdense t
  have hQ : Q.card = q := hl.1
  have hline : ∀ z ∈ Q, z.2.2+b*z.1.2 = u.2.2+b*u.1.2 := by
    rcases hl.2 with ⟨x,hx⟩ | ⟨d,w,hw⟩
    · have hu' := hx u hu rfl
      have hv' := hx v hv hK.symm
      exact False.elim (hdx (hu'.trans hv'.symm))
    · have hu' := hw u hu rfl
      have hv' := hw v hv hK.symm
      have hdb : d = b := by
        apply (mul_right_inj' (sub_ne_zero.mpr hdx)).mp
        linear_combination hu' - hv' - hL
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      have hzw := hw z hz'.1 hz'.2
      rw [hdb] at hu' hzw
      exact hzw.trans hu'.symm
  intro a' ha' hgood'
  let f (z : ((K × L) × (K × L))) := z.2.1 + a'*z.1.1
  have hf : Set.InjOn f Q := by
    intro z hz z' hz' he
    have hzS := (Finset.mem_filter.mp hz).1
    have hz'S := (Finset.mem_filter.mp hz').1
    apply hgood' hzS hz'S
    apply Prod.ext
    · exact he
    · exact (hline z hz).trans (hline z' hz').symm
  have hle : Q.card ≤ Fintype.card K := by
    calc
      Q.card = (Q.image f).card := (Finset.card_image_of_injOn hf).symm
      _ ≤ Fintype.card K := Finset.card_le_univ _
  omega
