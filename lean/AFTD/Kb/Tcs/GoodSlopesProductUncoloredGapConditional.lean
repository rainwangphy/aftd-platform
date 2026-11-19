import AFTD.Prelude
import AFTD.Kb.Tcs.GoodSlopesProductDenseRowBadColumnConditional

/-!
# good_slopes_product_uncolored_gap_conditional

Topic: combinatorics   Node: 733770ce5102

Provenance: helper lemma. Conditional product-fiber gap reductions for OP-1027; finite-field direction hypotheses compare arXiv:2611.04551 Lemma 2.7.

For finite fields of odd sizes 5≤p and q≥2p−1, assuming the q-point finite-field direction theorem, a pq-point set with a bad unit-coordinate direction has at most (p−1)(q−2) good unit-coordinate directions.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_product_uncolored_gap_conditional (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (p q : ℕ) (hp : Fintype.card K = p) (hq : Fintype.card L = q)
    (hp5 : 5 ≤ p) (hpodd : p % 2 = 1) (hqodd : q % 2 = 1) (hsep : 2*p-1 ≤ q)
    (hdirL : (∀ T : Finset (L × L), T.card = q →
      (∃ G : Finset L, (q+1)/2 ≤ G.card ∧ ∀ b ∈ G, Set.InjOn (fun z : L × L => z.2 + b*z.1) T) →
      (∃ x : L, ∀ z ∈ T, z.1 = x) ∨ (∃ b t : L, ∀ z ∈ T, z.2 + b*z.1 = t))) (S : Finset ((K × L) × (K × L))) (hcard : S.card = p*q)
    (hbad : ∃ a : K, a ≠ 0 ∧ ∃ b : L, b ≠ 0 ∧ ¬ Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S) :
    ((Finset.univ : Finset (K × L)).filter fun ab => ab.1 ≠ 0 ∧ ab.2 ≠ 0 ∧ Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + ab.1*z.1.1, z.2.2 + ab.2*z.1.2)) S).card ≤ (p-1)*(q-1)-(p-1) := by
  classical
  let UK : Finset K := Finset.univ.filter fun a => a ≠ 0
  let UL : Finset L := Finset.univ.filter fun b => b ≠ 0
  have hUK : UK.card = p-1 := by
    have heq : UK = Finset.univ.erase (0 : K) := by ext a; simp [UK]
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, hp]
  have hUL : UL.card = q-1 := by
    have heq : UL = Finset.univ.erase (0 : L) := by ext b; simp [UL]
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, hq]
  let U : Finset (K × L) := UK ×ˢ UL
  let D : Finset (K × L) := (Finset.univ : Finset (K × L)).filter fun ab => ab.1 ≠ 0 ∧ ab.2 ≠ 0 ∧
    Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1+ab.1*z.1.1,z.2.2+ab.2*z.1.2)) S
  let G (a : K) : Finset L := UL.filter fun b =>
    Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1+a*z.1.1,z.2.2+b*z.1.2)) S
  have hU : U.card = (p-1)*(q-1) := by dsimp [U]; rw [Finset.card_product,hUK,hUL]
  have hDU : D ⊆ U := by
    intro ab hab
    have h := (Finset.mem_filter.mp hab).2
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2.1⟩⟩
  have hGsub (a : K) : G a ⊆ UL := Finset.filter_subset _ _
  have hmissing : p-1 ≤ (U \ D).card := by
    by_cases hsparse : ∃ a : K, a ≠ 0 ∧ (G a).card < (q+1)/2
    · obtain ⟨a,ha,hsmall⟩ := hsparse
      let Bad : Finset (K × L) := (UL \ G a).image (fun b => (a,b))
      have hBad : Bad.card = (q-1)-(G a).card := by
        dsimp [Bad]
        rw [Finset.card_image_of_injective _ (fun b c h => congrArg Prod.snd h),
          Finset.card_sdiff_of_subset (hGsub a),hUL]
      have hsub : Bad ⊆ U \ D := by
        intro ab hab
        obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hab
        have hb' := Finset.mem_sdiff.mp hb
        have hbu := (Finset.mem_filter.mp hb'.1).2
        apply Finset.mem_sdiff.mpr
        constructor
        · exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,hb'.1⟩
        · intro hd
          have hgood := (Finset.mem_filter.mp hd).2.2.2
          exact hb'.2 (Finset.mem_filter.mpr ⟨hb'.1,hgood⟩)
      have hcardBad := Finset.card_le_card hsub
      omega
    · push Not at hsparse
      obtain ⟨a,ha,b,hb,hbBad⟩ := hbad
      have hdense : (q+1)/2 ≤ (G a).card := hsparse a ha
      have hdense' : (q+1)/2 ≤ ((Finset.univ : Finset L).filter fun c => c ≠ 0 ∧
          Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1+a*z.1.1,z.2.2+c*z.1.2)) S).card := by
        simpa [G,UL,Finset.filter_filter, and_assoc] using hdense
      have hcol := good_slopes_product_dense_row_bad_column_conditional K L p q hp hq (by omega)
        hdirL S hcard a ha hdense' b hb hbBad
      let Bad : Finset (K × L) := UK.image (fun a' => (a',b))
      have hBad : Bad.card = p-1 := by
        dsimp [Bad]
        rw [Finset.card_image_of_injective _ (fun a a' h => congrArg Prod.fst h),hUK]
      have hsub : Bad ⊆ U \ D := by
        intro ab hab
        obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp hab
        have ha'0 := (Finset.mem_filter.mp ha').2
        apply Finset.mem_sdiff.mpr
        constructor
        · exact Finset.mem_product.mpr ⟨ha',Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩⟩
        · intro hd
          exact hcol a' ha'0 ((Finset.mem_filter.mp hd).2.2.2)
      have hcardBad := Finset.card_le_card hsub
      omega
  have hsubcard := Finset.card_sdiff_of_subset hDU
  have hD : D.card ≤ (p-1)*(q-1)-(p-1) := by omega
  exact hD
