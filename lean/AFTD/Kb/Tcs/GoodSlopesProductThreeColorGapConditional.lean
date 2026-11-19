import AFTD.Prelude
import AFTD.Kb.Tcs.GoodSlopesColoredProductRowsConditional

/-!
# good_slopes_product_three_color_gap_conditional

Topic: combinatorics   Node: ffeeb221c9a8

Provenance: helper lemma. Conditional product-fiber gap reductions for OP-1027; finite-field direction hypotheses compare arXiv:2611.04551 Lemma 2.7.

For finite fields of odd sizes 5≤p and q≥2p−1 with 3(p+1)<2q, assume both finite-field direction classifications. A three-colored pq-point set with a bad unit-coordinate direction has at most (p−1)(q−3) good unit-coordinate directions.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
private theorem in962_many_dense_rows {α : Type*} [DecidableEq α]
    (R : Finset α) (g : α → ℕ) (p q : ℕ)
    (hp5 : 5 ≤ p) (hpodd : p % 2 = 1) (hqodd : q % 2 = 1) (hsep : 2*p-1 ≤ q)
    (hR : R.card = p-1) (hg : ∀ a ∈ R, g a ≤ q-1)
    (hlarge : (p-1)*(q-3) < ∑ a ∈ R, g a) :
    (p+1)/2 ≤ (R.filter fun a => (q+1)/2 ≤ g a).card := by
  classical
  let D := R.filter fun a => (q+1)/2 ≤ g a
  let N := R \ D
  have hDR : D ⊆ R := Finset.filter_subset _ _
  have hcard : N.card + D.card = p-1 := by
    have h := Finset.card_sdiff_add_card_eq_card hDR
    simpa [N,hR] using h
  have hsum : (∑ a ∈ R, g a) = (∑ a ∈ D, g a) + ∑ a ∈ N, g a := by
    have h := Finset.sum_sdiff hDR (f := g)
    simpa [N,add_comm] using h.symm
  let k := (p-1)/2
  let l := (q-1)/2
  have hp1 : p-1 = 2*k := by dsimp [k]; omega
  have hq1 : q-1 = 2*l := by dsimp [l]; omega
  have hq3 : q-3+2 = 2*l := by dsimp [l]; omega
  have hl4 : 4 ≤ l := by dsimp [l]; omega
  change (p+1)/2 ≤ D.card
  by_contra hnot
  have hd : D.card ≤ k := by dsimp [k]; omega
  have hsD : (∑ a ∈ D, g a) ≤ D.card*(2*l) := by
    calc
      _ ≤ ∑ _a ∈ D, (2*l) := by
        apply Finset.sum_le_sum
        intro a ha
        have haR := hDR ha
        have hh := hg a haR
        omega
      _ = D.card*(2*l) := by simp
  have hsN : (∑ a ∈ N, g a) ≤ N.card*l := by
    calc
      _ ≤ ∑ _a ∈ N, l := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' := Finset.mem_sdiff.mp ha
        have hn : ¬ (q+1)/2 ≤ g a := by
          intro ht
          exact ha'.2 (Finset.mem_filter.mpr ⟨ha'.1,ht⟩)
        dsimp [l]
        omega
      _ = N.card*l := by simp
  have hdl : D.card*l ≤ k*l := Nat.mul_le_mul_right l hd
  have hlk : 4*k ≤ k*l := by
    have h := Nat.mul_le_mul_left k hl4
    simpa [Nat.mul_comm] using h
  have hc : N.card+D.card = 2*k := by omega
  have hsumprod : N.card*l+D.card*l = 2*k*l := by
    calc
      _ = (N.card+D.card)*l := by ring
      _ = 2*k*l := by rw [hc]
  have htotal : (∑ a ∈ R, g a) ≤ 3*k*l := by nlinarith
  have hbase : (p-1)*(q-3)+4*k = 4*k*l := by
    rw [hp1]
    calc
      2*k*(q-3)+4*k = 2*k*((q-3)+2) := by ring
      _ = 4*k*l := by rw [hq3]; ring
  nlinarith

theorem good_slopes_product_three_color_gap_conditional (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (p q : ℕ) (hp : Fintype.card K = p) (hq : Fintype.card L = q)
    (hp5 : 5 ≤ p) (hpodd : p % 2 = 1) (hqodd : q % 2 = 1) (hsep : 2*p-1 ≤ q) (hsize : (p+1)*3 < 2*q)
    (hdirK : (∀ T : Finset (K × K), T.card = p →
      (∃ G : Finset K, (p+1)/2 ≤ G.card ∧ ∀ b ∈ G, Set.InjOn (fun z : K × K => z.2 + b*z.1) T) →
      (∃ x : K, ∀ z ∈ T, z.1 = x) ∨ (∃ b t : K, ∀ z ∈ T, z.2 + b*z.1 = t))) (hdirL : (∀ T : Finset (L × L), T.card = q →
      (∃ G : Finset L, (q+1)/2 ≤ G.card ∧ ∀ b ∈ G, Set.InjOn (fun z : L × L => z.2 + b*z.1) T) →
      (∃ x : L, ∀ z ∈ T, z.1 = x) ∨ (∃ b t : L, ∀ z ∈ T, z.2 + b*z.1 = t))) (S : Finset ((K × L) × (K × L))) (color : ((K × L) × (K × L)) → Fin 3) (hcard : S.card = p*q)
    (hx : ∀ u ∈ S, ∀ v ∈ S, color u = color v → u.1 = v.1 → u = v)
    (hc : ∀ a : K, a ≠ 0 → ∀ b : L, b ≠ 0 → ∀ u ∈ S, ∀ v ∈ S, color u = color v →
      (u.2.1 + a*u.1.1, u.2.2 + b*u.1.2) = (v.2.1 + a*v.1.1, v.2.2 + b*v.1.2) → u = v)
    (hbad : ∃ a : K, a ≠ 0 ∧ ∃ b : L, b ≠ 0 ∧ ¬ Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S) :
    ((Finset.univ : Finset (K × L)).filter fun ab => ab.1 ≠ 0 ∧ ab.2 ≠ 0 ∧ Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + ab.1*z.1.1, z.2.2 + ab.2*z.1.2)) S).card ≤ (p-1)*(q-1)-2*(p-1) := by
  classical
  let UK : Finset K := Finset.univ.filter fun a => a ≠ 0
  let UL : Finset L := Finset.univ.filter fun b => b ≠ 0
  let Good : Finset (K × L) := (Finset.univ : Finset (K × L)).filter fun ab =>
    ab.1 ≠ 0 ∧ ab.2 ≠ 0 ∧ Set.InjOn (fun z : ((K × L) × (K × L)) =>
      (z.2.1+ab.1*z.1.1,z.2.2+ab.2*z.1.2)) S
  let G (a : K) : Finset L := UL.filter fun b =>
    Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1+a*z.1.1,z.2.2+b*z.1.2)) S
  have hUK : UK.card = p-1 := by
    have heq : UK = Finset.univ.erase (0 : K) := by ext a; simp [UK]
    rw [heq,Finset.card_erase_of_mem (Finset.mem_univ 0),Finset.card_univ,hp]
  have hUL : UL.card = q-1 := by
    have heq : UL = Finset.univ.erase (0 : L) := by ext b; simp [UL]
    rw [heq,Finset.card_erase_of_mem (Finset.mem_univ 0),Finset.card_univ,hq]
  have hGle (a : K) : (G a).card ≤ q-1 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hUL
  have hGoodMap : ∀ ab ∈ Good, ab.1 ∈ UK := by
    intro ab hab
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hab).2.1⟩
  have hfiber (a : K) (ha : a ∈ UK) :
      (Good.filter fun ab => ab.1 = a).card = (G a).card := by
    have hπ : Set.InjOn (fun ab : K × L => ab.2) (Good.filter fun ab => ab.1 = a) := by
      intro ab hab cd hcd he
      apply Prod.ext
      · exact (Finset.mem_filter.mp hab).2.trans (Finset.mem_filter.mp hcd).2.symm
      · exact he
    have himg : (Good.filter fun ab => ab.1 = a).image (fun ab : K × L => ab.2) = G a := by
      ext b
      constructor
      · intro hb
        obtain ⟨⟨a',b'⟩,hmem,he⟩ := Finset.mem_image.mp hb
        have hp' := Finset.mem_filter.mp hmem
        have hgood := (Finset.mem_filter.mp hp'.1).2
        have hfst := hp'.2
        change a' = a at hfst
        change b' = b at he
        subst a'
        subst b'
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgood.2.1⟩,hgood.2.2⟩
      · intro hb
        have hb' := Finset.mem_filter.mp hb
        have hb0 := (Finset.mem_filter.mp hb'.1).2
        have ha0 := (Finset.mem_filter.mp ha).2
        refine Finset.mem_image.mpr ⟨(a,b), ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨?_,rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha0,hb0,hb'.2⟩
    calc
      _ = ((Good.filter fun ab => ab.1 = a).image (fun ab : K × L => ab.2)).card := (Finset.card_image_of_injOn hπ).symm
      _ = (G a).card := by rw [himg]
  have hsum : Good.card = ∑ a ∈ UK, (G a).card := by
    calc
      _ = ∑ a ∈ UK, (Good.filter fun ab => ab.1 = a).card :=
        Finset.card_eq_sum_card_fiberwise hGoodMap
      _ = ∑ a ∈ UK, (G a).card := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hfiber a ha
  have hq3 : q-3+2=q-1 := by omega
  have hbase : (p-1)*(q-1) = (p-1)*(q-3)+2*(p-1) := by
    calc
      _ = (p-1)*((q-3)+2) := by rw [hq3]
      _ = (p-1)*(q-3)+2*(p-1) := by ring
  have heq : (p-1)*(q-1)-2*(p-1) = (p-1)*(q-3) := by omega
  change Good.card ≤ _
  rw [heq]
  by_contra hnot
  have hlarge : (p-1)*(q-3) < ∑ a ∈ UK, (G a).card := by rw [←hsum]; omega
  have hdense := in962_many_dense_rows UK (fun a => (G a).card) p q hp5 hpodd hqodd hsep hUK
    (fun a _ => hGle a) hlarge
  have hD : (UK.filter fun a => (q+1)/2 ≤ (G a).card) =
      (Finset.univ : Finset K).filter (fun a => a ≠ 0 ∧ (q+1)/2 ≤
        ((Finset.univ : Finset L).filter fun b => b ≠ 0 ∧
          Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1+a*z.1.1,z.2.2+b*z.1.2)) S).card) := by
    ext a
    simp [UK,G,UL,Finset.filter_filter,and_assoc]
  rw [hD] at hdense
  have htwo : 2 ≤ (p+1)/2 := by omega
  have hrows : max 2 ((p+1)/2) ≤ _ := max_le (le_trans htwo hdense) hdense
  have hall := good_slopes_colored_product_rows_conditional K L p q 3 hp hq (by omega) (by omega)
    hsize hdirK hdirL S color hcard hx hc hrows
  obtain ⟨a,ha,b,hb,hbad⟩ := hbad
  exact hbad (hall a ha b hb)
