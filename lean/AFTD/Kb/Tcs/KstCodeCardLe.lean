import AFTD.Prelude
import AFTD.Kb.Tcs.IsKstCode
import AFTD.Kb.Tcs.CardSimpleGraph

/-!
# kst_code_card_le

Topic: combinatorics   Node: 47a50de7b34a

Provenance: helper lemma. arXiv:2610.35136, Sharp Bounds for Graph-Codes Avoiding Complete Bipartite Differences, Proposition 3.2

Let s, t, n be natural numbers with 1 ≤ s, 1 ≤ t, and s + t ≤ n. Every K_{s,t}-code C of simple graphs on vertex set [n] has cardinality at most 2^{n choose 2 - 1}.
-/

open SimpleGraph

private lemma kst_code_card_le_between_top_ne_bot {V : Type*} (s t : Set V) (a b : V)
    (ha : a ∈ s) (hb : b ∈ t) (hab : a ≠ b) :
    (⊤ : SimpleGraph V).between s t ≠ ⊥ := by
  intro h
  have hadj : ((⊤ : SimpleGraph V).between s t).Adj a b := by
    rw [between_adj]
    exact ⟨hab, Or.inl ⟨ha, hb⟩⟩
  rw [h, bot_adj] at hadj
  exact hadj

private lemma kst_code_card_le_exists_disjoint_nonempty_finsets (s t n : ℕ)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hn : s + t ≤ n) :
    ∃ (A B : Finset (Fin n)) (a b : Fin n),
      Disjoint A B ∧ A.card = s ∧ B.card = t ∧ a ∈ A ∧ b ∈ B ∧ a ≠ b := by
  have h_univ : s + t ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_fin]
    exact hn
  obtain ⟨U, -, hU⟩ := Finset.exists_subset_card_eq h_univ
  have hs_le : s ≤ U.card := by rw [hU]; exact Nat.le_add_right s t
  obtain ⟨A, hAU, hA⟩ := Finset.exists_subset_card_eq hs_le
  have hB_card : (U \ A).card = t := by
    rw [Finset.card_sdiff_of_subset hAU, hU, hA, Nat.add_sub_cancel_left]
  have hA_pos : 0 < A.card := by omega
  have hB_pos : 0 < (U \ A).card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hA_pos
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hB_pos
  have hab : a ≠ b := by
    rintro rfl
    exact (Finset.mem_sdiff.mp hb).2 ha
  exact ⟨A, U \ A, a, b, disjoint_sdiff_self_right, hA, hB_card, ha, hb, hab⟩

private lemma kst_code_card_le_disjoint_image_symmDiff (s t n : ℕ) (C : Set (SimpleGraph (Fin n)))
    (hC : is_kst_code s t n C) (A B : Finset (Fin n)) (hdisj : Disjoint A B)
    (hA : A.card = s) (hB : B.card = t)
    (H : SimpleGraph (Fin n)) (hH_def : H = (⊤ : SimpleGraph (Fin n)).between (A : Set (Fin n)) (B : Set (Fin n)))
    (hH_ne : H ≠ ⊥) :
    Disjoint C ((fun G => symmDiff G H) '' C) := by
  rw [Set.disjoint_left]
  rintro _ hx ⟨G, hG, rfl⟩
  have hne : G ≠ symmDiff G H := by
    intro heq
    have h1 : symmDiff G ⊥ = symmDiff G H := by
      rw [symmDiff_bot]
      exact heq
    rw [symmDiff_right_inj] at h1
    exact hH_ne h1.symm
  have hdiff : symmDiff G (symmDiff G H) = H := symmDiff_symmDiff_cancel_left G H
  have hnot := hC hG hx hne A B hdisj hA hB
  rw [← hH_def] at hnot
  exact hnot hdiff

/-- Upper bound on the size of a K_{s,t}-code for s, t ≥ 1 and n ≥ s + t. -/
theorem kst_code_card_le (s t n : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hn : s + t ≤ n)
    (C : Set (SimpleGraph (Fin n))) (hC : is_kst_code s t n C) :
    Set.ncard C ≤ 2 ^ (n.choose 2 - 1) := by
  obtain ⟨A, B, a, b, hdisj, hA, hB, ha, hb, hab⟩ :=
    kst_code_card_le_exists_disjoint_nonempty_finsets s t n hs ht hn
  set H : SimpleGraph (Fin n) := (⊤ : SimpleGraph (Fin n)).between (A : Set (Fin n)) (B : Set (Fin n))
  have hH_ne : H ≠ ⊥ := kst_code_card_le_between_top_ne_bot (A : Set (Fin n)) (B : Set (Fin n)) a b ha hb hab
  have hdisj_sets := kst_code_card_le_disjoint_image_symmDiff s t n C hC A B hdisj hA hB H rfl hH_ne
  have hinj : Function.Injective (fun G : SimpleGraph (Fin n) => symmDiff G H) := by
    intro G₁ G₂ h
    rwa [symmDiff_left_inj] at h
  have h_img_card : ((fun G => symmDiff G H) '' C).ncard = C.ncard :=
    Set.ncard_image_of_injective C hinj
  have h_union : (C ∪ (fun G => symmDiff G H) '' C).ncard = C.ncard + C.ncard := by
    rw [Set.ncard_union_eq hdisj_sets (Set.toFinite C) (Set.toFinite _), h_img_card]
  have h_le_univ : (C ∪ (fun G => symmDiff G H) '' C).ncard ≤ (Set.univ : Set (SimpleGraph (Fin n))).ncard :=
    Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  have h_univ : (Set.univ : Set (SimpleGraph (Fin n))).ncard = 2 ^ (n.choose 2) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, card_simpleGraph, Fintype.card_fin]
  rw [h_union, h_univ] at h_le_univ
  have hn2 : 2 ≤ n := by omega
  have hk : 1 ≤ n.choose 2 := Nat.choose_pos hn2
  have hk' : n.choose 2 = (n.choose 2 - 1) + 1 := by omega
  rw [hk', pow_succ] at h_le_univ
  omega
