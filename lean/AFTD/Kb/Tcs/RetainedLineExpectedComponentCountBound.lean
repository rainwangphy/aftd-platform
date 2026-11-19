import AFTD.Prelude
import AFTD.Kb.Tcs.RetainedLineTruncate
import AFTD.Kb.Tcs.RetainedLineComponentCountLeLeftRoots

/-!
# retained_line_expected_component_count_bound

Topic: algorithms   Node: 6472c9024878

Provenance: helper lemma. OP-815: finite-volume expected component-density bound.

For n line vertices with each possible edge independently retained with probability q in [0,1], the expected number of connected components after deleting edges of length greater than k is at most the sum over vertices v of (1-q) to the power min(k,v).
-/

private lemma retained_line_expected_component_count_bound_sum_powerset
    {α : Type*} [DecidableEq α] (q : ℝ) (E F : Finset α) (hF : F ⊆ E) :
    (∑ S ∈ E.powerset,
        q ^ S.card * (1 - q) ^ (E.card - S.card) *
          (if Disjoint F S then (1 : ℝ) else 0))
      = (1 - q) ^ F.card := by
  classical
  have hfilter : E.powerset.filter (fun S => Disjoint F S) = (E \ F).powerset := by
    ext S
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powerset, Finset.subset_sdiff]
    exact ⟨fun h => ⟨h.1, disjoint_comm.mp h.2⟩, fun h => ⟨h.1, disjoint_comm.mp h.2⟩⟩
  have hsum : (∑ S ∈ (E \ F).powerset,
      q ^ S.card * (1 - q) ^ ((E \ F).card - S.card)) = 1 := by
    rw [Finset.sum_pow_mul_eq_add_pow]
    simp
  calc
    (∑ S ∈ E.powerset,
        q ^ S.card * (1 - q) ^ (E.card - S.card) *
          (if Disjoint F S then (1 : ℝ) else 0))
        = ∑ S ∈ (E \ F).powerset,
            q ^ S.card * (1 - q) ^ (E.card - S.card) := by
          rw [← hfilter, Finset.sum_filter]
          simp
    _ = (1 - q) ^ F.card * ∑ S ∈ (E \ F).powerset,
            q ^ S.card * (1 - q) ^ ((E \ F).card - S.card) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro S hS
          have hSle : S.card ≤ (E \ F).card := Finset.card_le_card (Finset.mem_powerset.mp hS)
          have hEcard : E.card = F.card + (E \ F).card := by
            rw [Nat.add_comm]
            exact (Finset.card_sdiff_add_card_eq_card hF).symm
          rw [hEcard, Nat.add_sub_assoc hSle, pow_add]
          ring
    _ = (1 - q) ^ F.card := by rw [hsum, mul_one]

private theorem retained_line_expected_component_count_bound_graph_sum
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℝ) (F : Finset (Sym2 V))
    (hF : (F : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ) :
    (by classical exact
      (∑ G : SimpleGraph V,
      q ^ G.edgeSet.ncard * (1 - q) ^ ((Fintype.card V).choose 2 - G.edgeSet.ncard) *
        (if Disjoint (F : Set (Sym2 V)) G.edgeSet then (1 : ℝ) else 0))
      = (1 - q) ^ F.card) := by
  classical
  let E : Finset (Sym2 V) := Sym2.diagSetᶜ.toFinset
  have hEcard : E.card = (Fintype.card V).choose 2 := by
    rw [show E = (Sym2.diagSetᶜ).toFinset from rfl, Set.toFinset_card,
      Sym2.card_diagSet_compl]
  have hFsubE : F ⊆ E := by
    intro e he
    simpa [E] using hF he
  have hfrom (S : Finset (Sym2 V)) (hS : S ⊆ E) :
      (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).edgeSet = S := by
    have hSset : (S : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ := by
      intro e he
      have heE : e ∈ E := hS he
      simpa [E] using heE
    have hSdiag : Disjoint (S : Set (Sym2 V)) Sym2.diagSet := by
      rw [Set.disjoint_left]
      intro e heS heDiag
      exact (hSset heS) heDiag
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact sdiff_eq_left.mpr hSdiag
  calc
    (∑ G : SimpleGraph V,
      q ^ G.edgeSet.ncard * (1 - q) ^ ((Fintype.card V).choose 2 - G.edgeSet.ncard) *
        (if Disjoint (F : Set (Sym2 V)) G.edgeSet then (1 : ℝ) else 0))
        = ∑ S ∈ E.powerset,
          q ^ S.card * (1 - q) ^ ((Fintype.card V).choose 2 - S.card) *
            (if Disjoint F S then (1 : ℝ) else 0) := by
          refine Finset.sum_bij (fun G _ => G.edgeFinset) ?_ ?_ ?_ ?_
          · intro G hG
            rw [Finset.mem_powerset]
            intro e he
            have heSet : e ∈ G.edgeSet := by
              simpa using (SimpleGraph.mem_edgeFinset.mp he)
            have heTop : e ∈ (⊤ : SimpleGraph V).edgeSet :=
              SimpleGraph.edgeSet_mono le_top heSet
            have heDiag : e ∈ Sym2.diagSetᶜ := by
              simpa [SimpleGraph.edgeSet_top] using heTop
            simpa [E] using heDiag
          · intro G₁ hG₁ G₂ hG₂ heq
            exact SimpleGraph.edgeFinset_inj.mp heq
          · intro S hS
            refine ⟨SimpleGraph.fromEdgeSet (S : Set (Sym2 V)), Finset.mem_univ _, ?_⟩
            apply Finset.coe_injective
            simp [SimpleGraph.coe_edgeFinset, hfrom S (Finset.mem_powerset.mp hS)]
          · intro G hG
            have hcardG : G.edgeSet.ncard = G.edgeFinset.card := by
              rw [SimpleGraph.edgeFinset]
              exact Set.ncard_eq_toFinset_card' G.edgeSet
            have hdisjG : Disjoint (F : Set (Sym2 V)) G.edgeSet ↔
                Disjoint F G.edgeFinset := by
              simpa [Finset.disjoint_coe, SimpleGraph.coe_edgeFinset] using
                (Finset.disjoint_coe (s := F) (t := G.edgeFinset))
            rw [hcardG]
            by_cases h : Disjoint (F : Set (Sym2 V)) G.edgeSet
            · have h' : Disjoint F G.edgeFinset := hdisjG.mp h
              simp [h, h']
            · have h' : ¬ Disjoint F G.edgeFinset := fun hh => h (hdisjG.mpr hh)
              simp [h, h']
    _ = ∑ S ∈ E.powerset,
          q ^ S.card * (1 - q) ^ (E.card - S.card) *
            (if Disjoint F S then (1 : ℝ) else 0) := by
          rw [hEcard]
    _ = (1 - q) ^ F.card :=
          retained_line_expected_component_count_bound_sum_powerset q E F hFsubE

private def retained_line_expected_component_count_bound_earlier_edges
    (n k : ℕ) (v : Fin n) : Finset (Sym2 (Fin n)) :=
  (Finset.univ : Finset (Fin (min k v.val))).image fun i =>
    s(v, ⟨v.val - 1 - i.val, by
      have hi : i.val < min k v.val := i.isLt
      have hmin : min k v.val ≤ v.val := min_le_right _ _
      omega⟩)

private lemma retained_line_expected_component_count_bound_earlier_edges_card
    (n k : ℕ) (v : Fin n) :
    (retained_line_expected_component_count_bound_earlier_edges n k v).card =
      min k v.val := by
  classical
  rw [retained_line_expected_component_count_bound_earlier_edges]
  rw [Finset.card_image_of_injOn]
  · simp
  · intro i hi j hj heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · apply Fin.ext
      have hval : v.val - 1 - i.val = v.val - 1 - j.val := by
        exact congrArg Fin.val hw
      have hi_lt : i.val < v.val := lt_of_lt_of_le i.isLt (min_le_right _ _)
      have hj_lt : j.val < v.val := lt_of_lt_of_le j.isLt (min_le_right _ _)
      omega
    · exfalso
      have hval : v.val - 1 - i.val = v.val := by
        exact congrArg Fin.val hw
      have hi_lt : i.val < v.val := lt_of_lt_of_le i.isLt (min_le_right _ _)
      omega

private lemma retained_line_expected_component_count_bound_earlier_edges_subset_diag
    (n k : ℕ) (v : Fin n) :
    (retained_line_expected_component_count_bound_earlier_edges n k v :
        Set (Sym2 (Fin n))) ⊆ Sym2.diagSetᶜ := by
  classical
  intro e he
  rw [retained_line_expected_component_count_bound_earlier_edges] at he
  rw [Finset.mem_coe, Finset.mem_image] at he
  rcases he with ⟨i, hi, rfl⟩
  rw [Set.mem_compl_iff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
  intro hveq
  have hval : v.val = v.val - 1 - i.val := congrArg Fin.val hveq
  have hi_lt : i.val < v.val := lt_of_lt_of_le i.isLt (min_le_right _ _)
  omega

private lemma retained_line_expected_component_count_bound_root_iff_disjoint
    (n k : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) :
    (∀ w : Fin n, w < v → ¬ (G.Adj v w ∧ Nat.dist v.val w.val ≤ k)) ↔
      Disjoint (retained_line_expected_component_count_bound_earlier_edges n k v :
        Set (Sym2 (Fin n))) G.edgeSet := by
  classical
  rw [Set.disjoint_left]
  constructor
  · intro hroot e he
    rw [retained_line_expected_component_count_bound_earlier_edges] at he
    rw [Finset.mem_coe, Finset.mem_image] at he
    rcases he with ⟨i, hi, rfl⟩
    intro heG
    rw [SimpleGraph.mem_edgeSet] at heG
    have hwlt : (⟨v.val - 1 - i.val, by
        have hi' : i.val < min k v.val := i.isLt
        have hmin : min k v.val ≤ v.val := min_le_right _ _
        omega⟩ : Fin n) < v := by
      rw [Fin.lt_def]
      change v.val - 1 - i.val < v.val
      have hi' : i.val < min k v.val := i.isLt
      have hmin : min k v.val ≤ v.val := min_le_right _ _
      omega
    have hdist : Nat.dist v.val (v.val - 1 - i.val) ≤ k := by
      have hi' : i.val < min k v.val := i.isLt
      have hmin : min k v.val ≤ k := min_le_left _ _
      rw [Nat.dist_eq_sub_of_le_right]
      · omega
      · omega
    exact hroot _ hwlt ⟨heG, hdist⟩
  · intro hdisj w hw hadj
    let d := min k v.val
    have hwv : w.val ≤ v.val := le_of_lt hw
    have hdist : Nat.dist v.val w.val ≤ k := hadj.2
    have hwlt : w.val < v.val := hw
    let i : Fin d := ⟨v.val - 1 - w.val, by
      have hd1 : v.val - 1 - w.val < k := by
        have h := hdist
        rw [Nat.dist_eq_sub_of_le_right hwv] at h
        omega
      have hd2 : v.val - 1 - w.val < v.val := by omega
      exact lt_min hd1 hd2⟩
    have he : s(v, w) ∈ retained_line_expected_component_count_bound_earlier_edges n k v := by
      rw [retained_line_expected_component_count_bound_earlier_edges]
      rw [Finset.mem_image]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      congr 1
      apply Fin.ext
      dsimp [i, d]
      omega
    have heG : s(v, w) ∈ G.edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hadj.1
    exact hdisj he heG

theorem retained_line_expected_component_count_bound (n k : ℕ) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
  (by classical exact ((Finset.univ : Finset (SimpleGraph (Fin n))).sum fun G =>
    q ^ G.edgeFinset.card * (1 - q) ^ (Nat.choose n 2 - G.edgeFinset.card) *
      (Nat.card (retained_line_truncate G k).ConnectedComponent : ℝ)) ≤
    ((Finset.univ : Finset (Fin n)).sum fun v => (1 - q) ^ min k v.val)) := by
  classical
  let W : SimpleGraph (Fin n) → ℝ := fun G =>
    q ^ G.edgeFinset.card * (1 - q) ^ (Nat.choose n 2 - G.edgeFinset.card)
  have hW_nonneg (G : SimpleGraph (Fin n)) : 0 ≤ W G := by
    dsimp [W]
    exact mul_nonneg (pow_nonneg hq.1 _) (pow_nonneg (sub_nonneg.mpr hq.2) _)
  have hncard (G : SimpleGraph (Fin n)) :
      (({v : Fin n | ∀ w : Fin n, w < v →
          ¬ (retained_line_truncate G k).Adj v w}).ncard : ℝ)
        = ∑ v : Fin n,
          if (∀ w : Fin n, w < v → ¬ (retained_line_truncate G k).Adj v w)
            then (1 : ℝ) else 0 := by
    rw [Set.ncard_eq_toFinset_card']
    rw [Set.toFinset_setOf]
    rw [Finset.card_filter]
    norm_cast
  calc
    (∑ G : SimpleGraph (Fin n),
      q ^ G.edgeFinset.card * (1 - q) ^ (Nat.choose n 2 - G.edgeFinset.card) *
        (Nat.card (retained_line_truncate G k).ConnectedComponent : ℝ))
        = ∑ G : SimpleGraph (Fin n),
            W G * (Nat.card (retained_line_truncate G k).ConnectedComponent : ℝ) := by
          rfl
    _ ≤ ∑ G : SimpleGraph (Fin n),
          W G * ∑ v : Fin n,
            if (∀ w : Fin n, w < v → ¬ (retained_line_truncate G k).Adj v w)
              then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro G hG
          apply mul_le_mul_of_nonneg_left
          · calc
              (Nat.card (retained_line_truncate G k).ConnectedComponent : ℝ)
                  ≤ (({v : Fin n | ∀ w : Fin n, w < v →
                      ¬ (retained_line_truncate G k).Adj v w}).ncard : ℝ) := by
                    exact_mod_cast retained_line_component_count_le_left_roots
                      (retained_line_truncate G k)
              _ = ∑ v : Fin n,
                    if (∀ w : Fin n, w < v →
                      ¬ (retained_line_truncate G k).Adj v w) then (1 : ℝ) else 0 :=
                    hncard G
          · exact hW_nonneg G
    _ = ∑ v : Fin n, ∑ G : SimpleGraph (Fin n),
          W G * (if (∀ w : Fin n, w < v →
              ¬ (retained_line_truncate G k).Adj v w) then (1 : ℝ) else 0) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ v : Fin n, (1 - q) ^ min k v.val := by
          apply Finset.sum_congr rfl
          intro v hv
          let Fv := retained_line_expected_component_count_bound_earlier_edges n k v
          have hroot (G : SimpleGraph (Fin n)) :
              (∀ w : Fin n, w < v → ¬ (retained_line_truncate G k).Adj v w) ↔
                Disjoint (Fv : Set (Sym2 (Fin n))) G.edgeSet := by
            dsimp [Fv]
            simpa [retained_line_truncate] using
              retained_line_expected_component_count_bound_root_iff_disjoint n k G v
          calc
            (∑ G : SimpleGraph (Fin n),
              W G * (if (∀ w : Fin n, w < v →
                  ¬ (retained_line_truncate G k).Adj v w) then (1 : ℝ) else 0))
                = ∑ G : SimpleGraph (Fin n),
                  q ^ G.edgeSet.ncard * (1 - q) ^ (Nat.choose n 2 - G.edgeSet.ncard) *
                    (if Disjoint (Fv : Set (Sym2 (Fin n))) G.edgeSet
                      then (1 : ℝ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro G hG
                  have hcardG : G.edgeFinset.card = G.edgeSet.ncard := by
                    rw [SimpleGraph.edgeFinset]
                    exact (Set.ncard_eq_toFinset_card' G.edgeSet).symm
                  dsimp [W]
                  rw [hcardG]
                  by_cases h : (∀ w : Fin n, w < v →
                      ¬ (retained_line_truncate G k).Adj v w)
                  · have h' : Disjoint (Fv : Set (Sym2 (Fin n))) G.edgeSet :=
                      (hroot G).mp h
                    rw [if_pos h, if_pos h']
                  · have h' : ¬ Disjoint (Fv : Set (Sym2 (Fin n))) G.edgeSet :=
                      fun hh => h ((hroot G).mpr hh)
                    rw [if_neg h, if_neg h']
            _ = (1 - q) ^ Fv.card := by
                  simpa [Fintype.card_fin] using
                    retained_line_expected_component_count_bound_graph_sum (V := Fin n) q Fv
                      (retained_line_expected_component_count_bound_earlier_edges_subset_diag n k v)
            _ = (1 - q) ^ min k v.val := by
                  rw [retained_line_expected_component_count_bound_earlier_edges_card]
