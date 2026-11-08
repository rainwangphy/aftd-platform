import AFTD.Prelude

/-!
# simple_graph_maximum_independent_set_weighted_overlap_of_clique_four

Topic: graphs   Node: 259a72a80f06

Provenance: helper lemma. Elementary maximum-independent-set exchange in the triangle packing-cover campaign; related graph background: https://arxiv.org/abs/2609.13831.

In a finite graph with no clique of size five, every nonnegative vertex weighting admits a maximum independent set whose weighted overlap score is at least three halves of the total weight, counting a vertex in the independent set with score three and any other vertex by its number of neighbors in the set.
-/

theorem simple_graph_maximum_independent_set_weighted_overlap_of_clique_four
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hclique : ∀ C : Finset V, G.IsClique C → C.card ≤ 4) :
    ∃ S : Finset V, G.IsIndepSet S ∧
      (∀ T : Finset V, G.IsIndepSet T → T.card ≤ S.card) ∧
      3 * (∑ v : V, w v) ≤
        6 * (∑ v ∈ S, w v) +
          2 * ∑ v ∈ (Finset.univ \ S), w v * ((S.filter (G.Adj v)).card : ℝ) := by
  classical
  obtain ⟨S, hS_indep, hS_maxcard, hS_maxweight⟩ :
      ∃ S : Finset V, G.IsIndepSet S ∧
        (∀ T : Finset V, G.IsIndepSet T → T.card ≤ S.card) ∧
        (∀ T : Finset V, G.IsIndepSet T → T.card = S.card →
          ∑ v ∈ T, w v ≤ ∑ v ∈ S, w v) := by
    let Fam : Finset (Finset V) := Finset.univ.filter (fun T => G.IsIndepSet T)
    have hne : Fam.Nonempty := ⟨∅, by simp [Fam]⟩
    obtain ⟨S0, hS0fam, hS0max⟩ := Finset.exists_max_image Fam (fun T => T.card) hne
    have hS0_indep : G.IsIndepSet S0 := by
      have h := hS0fam; simp only [Fam, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h
    let Fam2 : Finset (Finset V) := Fam.filter (fun T => T.card = S0.card)
    have hne2 : Fam2.Nonempty := ⟨S0, by simp [Fam2, hS0fam]⟩
    obtain ⟨S, hSfam2, hSmax⟩ := Finset.exists_max_image Fam2 (fun T => ∑ v ∈ T, w v) hne2
    have hSfam : S ∈ Fam := (Finset.mem_filter.mp hSfam2).1
    have hScard : S.card = S0.card := (Finset.mem_filter.mp hSfam2).2
    have hS_indep : G.IsIndepSet S := by
      have h := hSfam; simp only [Fam, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h
    refine ⟨S, hS_indep, ?_, ?_⟩
    · intro T hT
      have hTFam : T ∈ Fam := by simp [Fam, hT]
      have hle := hS0max T hTFam
      omega
    · intro T hT hTc
      have hTfam : T ∈ Fam := by simp [Fam, hT]
      have hTcard : T.card = S0.card := by omega
      have hTfam2 : T ∈ Fam2 := by simp [Fam2, hTfam, hTcard]
      exact hSmax T hTfam2
  refine ⟨S, hS_indep, hS_maxcard, ?_⟩
  set B : Finset V := Finset.univ \ S with hB
  have hB_notS : ∀ v ∈ B, v ∉ S := by
    intro v hv
    rw [hB] at hv
    exact (Finset.mem_sdiff.mp hv).2
  have indep_ins : ∀ (A : Finset V) (s v : V), G.IsIndepSet A →
      (∀ a ∈ A, a ≠ s → ¬ G.Adj v a) → G.IsIndepSet ((insert v (A.erase s) : Finset V) : Set V) := by
    intro A s v hA hv
    rw [SimpleGraph.IsIndepSet, Set.Pairwise] at hA ⊢
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at ha hb
    rcases ha with hav | ⟨ha_ne, haA⟩
    · rcases hb with hbv | ⟨hb_ne, hbA⟩
      · rw [hav, hbv] at hab ⊢; exact absurd rfl hab
      · rw [hav]; exact hv b hbA hb_ne
    · rcases hb with hbv | ⟨hb_ne, hbA⟩
      · rw [hbv]; intro h; exact hv a haA ha_ne ((G.adj_comm a v).mp h)
      · exact hA haA hbA hab
  have hB_pos : ∀ v ∈ B, 1 ≤ (S.filter (G.Adj v)).card := by
    intro v hv
    by_contra h
    have hcard0 : (S.filter (G.Adj v)).card = 0 := by omega
    have hvS := hB_notS v hv
    have hno : ∀ a ∈ S, ¬ G.Adj v a := by
      intro a ha hadj
      have hmem : a ∈ S.filter (G.Adj v) := Finset.mem_filter.mpr ⟨ha, hadj⟩
      rw [Finset.card_eq_zero.mp hcard0] at hmem
      exact Finset.notMem_empty a hmem
    have hins : G.IsIndepSet ((insert v (S.erase v) : Finset V) : Set V) := by
      exact indep_ins S v v hS_indep (fun a ha _ => hno a ha)
    rw [Finset.erase_eq_of_notMem hvS] at hins
    have hc : (insert v S).card = S.card + 1 := Finset.card_insert_of_notMem hvS
    have hle := hS_maxcard (insert v S) hins
    rw [hc] at hle
    omega
  have priv_uniq : ∀ (v s : V), v ∈ B → (S.filter (G.Adj v)).card = 1 → s ∈ S → G.Adj v s →
      ∀ a ∈ S, G.Adj v a → a = s := by
    intro v s hvB hcard hsS hadj a haS hadja
    by_contra hne
    have hsub : ({a, s} : Finset V) ⊆ S.filter (G.Adj v) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨haS, hadja⟩
      · exact Finset.mem_filter.mpr ⟨hsS, hadj⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_pair hne, hcard] at hle
    omega
  set P : Finset V := B.filter (fun v => (S.filter (G.Adj v)).card = 1) with hP
  have hPsub : P ⊆ B := by rw [hP]; exact Finset.filter_subset _ _
  have hPprop : ∀ v ∈ P, (S.filter (G.Adj v)).card = 1 := by
    intro v hv
    rw [hP] at hv
    exact (Finset.mem_filter.mp hv).2
  have hPfiber : ∑ v ∈ P, w v = ∑ s ∈ S, ∑ v ∈ P.filter (fun v => G.Adj v s), w v := by
    have h1 : ∀ s : V, (∑ v ∈ P.filter (fun v => G.Adj v s), w v)
        = ∑ v ∈ P, (if G.Adj v s then w v else 0) := by
      intro s; rw [Finset.sum_filter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro v hv
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, hPprop v hv]
    simp
  have hfiber_weight : ∀ s ∈ S, ∀ v ∈ P.filter (fun v => G.Adj v s), w v ≤ w s := by
    intro s hs v hv
    simp only [Finset.mem_filter] at hv
    obtain ⟨hvP, hvs⟩ := hv
    have hvB : v ∈ B := hPsub hvP
    have hcard : (S.filter (G.Adj v)).card = 1 := hPprop v hvP
    have hvS : v ∉ S := hB_notS v hvB
    have hins : G.IsIndepSet ((insert v (S.erase s) : Finset V) : Set V) := by
      apply indep_ins S s v hS_indep
      intro a ha hane hadj
      exact hane (priv_uniq v s hvB hcard hs hvs a ha hadj)
    have hcardT : (insert v (S.erase s) : Finset V).card = S.card := by
      rw [Finset.card_insert_of_notMem (by simp [Finset.mem_erase, hvS]),
          Finset.card_erase_of_mem hs]
      have : 0 < S.card := Finset.card_pos.mpr ⟨s, hs⟩
      omega
    have hle := hS_maxweight (insert v (S.erase s)) hins hcardT
    have hsum : ∑ x ∈ (insert v (S.erase s) : Finset V), w x = w v + (∑ x ∈ S, w x - w s) := by
      rw [Finset.sum_insert (by simp [Finset.mem_erase, hvS])]
      have h := Finset.sum_erase_add (s := S) (f := w) hs
      linarith
    rw [hsum] at hle
    linarith
  have hfiber_card : ∀ s ∈ S, (P.filter (fun v => G.Adj v s)).card ≤ 3 := by
    intro s hs
    have hsnot : s ∉ P.filter (fun v => G.Adj v s) := by
      simp only [Finset.mem_filter]
      rintro ⟨hps, hadj⟩
      exact hB_notS s (hPsub hps) hs
    have hcl : G.IsClique ((insert s (P.filter (fun v => G.Adj v s)) : Finset V) : Set V) := by
      rw [SimpleGraph.IsClique, Set.Pairwise]
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_filter] at ha hb
      rcases ha with hav | ⟨haP, haAdj⟩
      · rcases hb with hbv | ⟨hbP, hbAdj⟩
        · rw [hav, hbv] at hab ⊢; exact absurd rfl hab
        · rw [hav]; exact (G.adj_comm b s).mp hbAdj
      · rcases hb with hbv | ⟨hbP, hbAdj⟩
        · rw [hbv]; exact haAdj
        · by_contra hnab
          exfalso
          have haB : a ∈ B := hPsub haP
          have hbB : b ∈ B := hPsub hbP
          have hca : (S.filter (G.Adj a)).card = 1 := hPprop a haP
          have hcb : (S.filter (G.Adj b)).card = 1 := hPprop b hbP
          have haS : a ∉ S := hB_notS a haB
          have hbS : b ∉ S := hB_notS b hbB
          have hA1 : G.IsIndepSet ((insert a (S.erase s) : Finset V) : Set V) := by
            apply indep_ins S s a hS_indep
            intro x hx hxne hadj
            exact hxne (priv_uniq a s haB hca hs haAdj x hx hadj)
          have hb_not : b ∉ (insert a (S.erase s) : Finset V) := by
            simp only [Finset.mem_insert, Finset.mem_erase]
            rintro (hba | ⟨hne, hbS'⟩)
            · exact hab hba.symm
            · exact hbS hbS'
          have hT : G.IsIndepSet ((insert b (insert a (S.erase s)) : Finset V) : Set V) := by
            rw [← Finset.erase_eq_of_notMem hb_not]
            apply indep_ins (insert a (S.erase s)) b b hA1
            intro x hx hxne hadj
            simp only [Finset.mem_insert, Finset.mem_erase] at hx
            rcases hx with hxa | ⟨hxs, hxS⟩
            · rw [hxa] at hadj
              exact hnab ((G.adj_comm b a).mp hadj)
            · exact hxs (priv_uniq b s hbB hcb hs hbAdj x hxS hadj)
          have hcardT : (insert b (insert a (S.erase s)) : Finset V).card = S.card + 1 := by
            rw [Finset.card_insert_of_notMem hb_not]
            rw [Finset.card_insert_of_notMem (by simp [Finset.mem_erase, haS])]
            rw [Finset.card_erase_of_mem hs]
            have : 0 < S.card := Finset.card_pos.mpr ⟨s, hs⟩
            omega
          have hle := hS_maxcard (insert b (insert a (S.erase s))) hT
          rw [hcardT] at hle
          omega
    have h4 := hclique _ hcl
    rw [Finset.card_insert_of_notMem hsnot] at h4
    omega
  have hWsplit : ∑ v : V, w v = ∑ v ∈ S, w v + ∑ v ∈ B, w v := by
    have h := Finset.sum_sdiff (f := w) (Finset.subset_univ S)
    rw [hB]
    linarith [h]
  have hsub : ∑ v ∈ B, (w v * (3 - 2 * ((S.filter (G.Adj v)).card : ℝ)))
      = 3 * (∑ v ∈ B, w v) - 2 * ∑ v ∈ B, w v * ((S.filter (G.Adj v)).card : ℝ) := by
    have heq : ∀ v ∈ B, w v * (3 - 2 * ((S.filter (G.Adj v)).card : ℝ))
        = 3 * w v - 2 * (w v * ((S.filter (G.Adj v)).card : ℝ)) := by
      intro v _; ring
    rw [Finset.sum_congr rfl heq, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  have hC : ∑ v ∈ B, (w v * (3 - 2 * ((S.filter (G.Adj v)).card : ℝ))) ≤ ∑ v ∈ P, w v := by
    rw [hP, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro v hv
    by_cases hc : (S.filter (G.Adj v)).card = 1
    · rw [if_pos hc, hc]; norm_num
    · rw [if_neg hc]
      have hge : 2 ≤ (S.filter (G.Adj v)).card := by have := hB_pos v hv; omega
      have hcoef : 3 - 2 * ((S.filter (G.Adj v)).card : ℝ) ≤ 0 := by
        have : (2:ℝ) ≤ ((S.filter (G.Adj v)).card : ℝ) := by exact_mod_cast hge
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (hw v) hcoef
  have hD : ∑ v ∈ P, w v ≤ 3 * ∑ s ∈ S, w s := by
    rw [hPfiber, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    calc ∑ v ∈ P.filter (fun v => G.Adj v s), w v
        ≤ ∑ v ∈ P.filter (fun v => G.Adj v s), w s := by
          apply Finset.sum_le_sum
          intro v hv; exact hfiber_weight s hs v hv
      _ = (P.filter (fun v => G.Adj v s)).card • w s := Finset.sum_const _
      _ = ((P.filter (fun v => G.Adj v s)).card : ℝ) * w s := by rw [nsmul_eq_mul]
      _ ≤ 3 * w s := by
          apply mul_le_mul_of_nonneg_right _ (hw s)
          exact_mod_cast hfiber_card s hs
  have hmain : 3 * (∑ v ∈ B, w v) - 2 * ∑ v ∈ B, w v * ((S.filter (G.Adj v)).card : ℝ)
      ≤ 3 * ∑ s ∈ S, w s := by
    rw [← hsub]
    linarith [hC, hD]
  rw [hWsplit]
  linarith [hmain]
