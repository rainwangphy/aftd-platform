import AFTD.Prelude
import AFTD.Kb.Tcs.IsKstCode
import AFTD.Kb.Tcs.IsBinaryLinearGraphCode
import AFTD.Kb.Tcs.CardSimpleGraph
import AFTD.Kb.Tcs.Weight

/-!
# kst_code_linear_construction_finite_field

Topic: combinatorics   Node: 1b1955e1c79e

Provenance: formalization of a published result. Source: arXiv:2610.35136 Lemma 4.2

Let n, s, t, r ≥ 1 be integers, and let w_1, ..., w_n in (ZMod 2)^r be vectors such that the sum of w_i over S is nonzero for every subset S of [n] with |S| in {s, t}. Then there exists a binary linear K_{s,t}-code C in the set of simple graphs on Fin n of codimension at most r (n.choose 2 - Nat.log 2 (Set.ncard C) ≤ r) and density at least (1/2)^r.
-/

/-- The weight `z i * z j` attached to an unordered pair of vertices. -/
noncomputable def kst_code_linear_construction_finite_field_edge_weight {n : ℕ} {F : Type*}
    [CommMonoid F] (z : Fin n → F) : Sym2 (Fin n) → F :=
  Sym2.lift ⟨fun i j => z i * z j, fun i j => mul_comm (z i) (z j)⟩

@[simp] lemma kst_code_linear_construction_finite_field_edge_weight_mk {n : ℕ} {F : Type*}
    [CommMonoid F] (z : Fin n → F) (i j : Fin n) :
    kst_code_linear_construction_finite_field_edge_weight z s(i, j) = z i * z j := rfl

/-- The syndrome of a graph: the sum of `z i * z j` over its edges. -/
noncomputable def kst_code_linear_construction_finite_field_syndrome {n : ℕ} {F : Type*}
    [CommSemiring F] (z : Fin n → F) (G : SimpleGraph (Fin n)) : F := by
  classical
  exact ∑ e : Sym2 (Fin n),
    if e ∈ G.edgeSet then kst_code_linear_construction_finite_field_edge_weight z e else 0

/-- The syndrome only depends on the set of edges. -/
lemma kst_code_linear_construction_finite_field_syndrome_eq_sum {n : ℕ} {F : Type*}
    [CommSemiring F] (z : Fin n → F) (G : SimpleGraph (Fin n)) (T : Finset (Sym2 (Fin n)))
    (hT : ∀ e, e ∈ T ↔ e ∈ G.edgeSet) :
    kst_code_linear_construction_finite_field_syndrome z G
      = ∑ e ∈ T, kst_code_linear_construction_finite_field_edge_weight z e := by
  classical
  have hg : ∀ x : Sym2 (Fin n), x ∉ T →
      (if x ∈ G.edgeSet then kst_code_linear_construction_finite_field_edge_weight z x else 0) = 0 := by
    intro x hx
    split_ifs with h
    · exact absurd ((hT x).mpr h) hx
    · rfl
  have h1 : (∑ e : Sym2 (Fin n),
        (if e ∈ G.edgeSet then kst_code_linear_construction_finite_field_edge_weight z e else 0))
      = ∑ e ∈ T,
        (if e ∈ G.edgeSet then kst_code_linear_construction_finite_field_edge_weight z e else 0) :=
    (Finset.sum_subset (Finset.subset_univ T) (fun x _ hx => hg x hx)).symm
  rw [kst_code_linear_construction_finite_field_syndrome, h1]
  refine Finset.sum_congr rfl (fun e he => ?_)
  split_ifs with h
  · rfl
  · exact absurd ((hT e).mp he) h

@[simp] lemma kst_code_linear_construction_finite_field_syndrome_bot {n : ℕ} {F : Type*}
    [CommSemiring F] (z : Fin n → F) :
    kst_code_linear_construction_finite_field_syndrome z (⊥ : SimpleGraph (Fin n)) = 0 := by
  classical
  simp [kst_code_linear_construction_finite_field_syndrome]

lemma kst_code_linear_construction_finite_field_syndrome_symmDiff {n : ℕ} {F : Type*}
    [CommSemiring F] [CharP F 2] (z : Fin n → F) (G G' : SimpleGraph (Fin n)) :
    kst_code_linear_construction_finite_field_syndrome z (symmDiff G G')
      = kst_code_linear_construction_finite_field_syndrome z G
        + kst_code_linear_construction_finite_field_syndrome z G' := by
  classical
  simp only [kst_code_linear_construction_finite_field_syndrome]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hmem : e ∈ (symmDiff G G').edgeSet ↔
      (e ∈ G.edgeSet ∧ e ∉ G'.edgeSet) ∨ (e ∉ G.edgeSet ∧ e ∈ G'.edgeSet) := by
    rw [symmDiff_def, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_sdiff,
      Set.mem_union, Set.mem_sdiff, Set.mem_sdiff]
    tauto
  by_cases h1 : e ∈ G.edgeSet <;> by_cases h2 : e ∈ G'.edgeSet <;>
    simp [hmem, h1, h2, CharTwo.add_self_eq_zero]

lemma kst_code_linear_construction_finite_field_syndrome_between {n : ℕ} {F : Type*}
    [CommSemiring F] (z : Fin n → F) (A B : Finset (Fin n)) (hAB : Disjoint A B) :
    kst_code_linear_construction_finite_field_syndrome z
        (SimpleGraph.between (A : Set (Fin n)) (B : Set (Fin n)) (⊤ : SimpleGraph (Fin n)))
      = (∑ a ∈ A, z a) * (∑ b ∈ B, z b) := by
  classical
  have hset : (Finset.univ.filter (fun e : Sym2 (Fin n) =>
        e ∈ (SimpleGraph.between (A : Set (Fin n)) (B : Set (Fin n)) (⊤ : SimpleGraph (Fin n))).edgeSet))
      = (A ×ˢ B).image (fun p : Fin n × Fin n => s(p.1, p.2)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_product]
    constructor
    · intro he
      induction e using Sym2.ind with
      | _ v w =>
        rw [SimpleGraph.mem_edgeSet, SimpleGraph.between_adj, SimpleGraph.top_adj] at he
        obtain ⟨-, hv | hv⟩ := he
        · exact ⟨(v, w), ⟨hv.1, hv.2⟩, rfl⟩
        · exact ⟨(w, v), ⟨hv.2, hv.1⟩, (Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)).symm⟩
    · rintro ⟨p, ⟨hpa, hpb⟩, rfl⟩
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.between_adj, SimpleGraph.top_adj]
      refine ⟨?_, Or.inl ⟨hpa, hpb⟩⟩
      intro h
      exact (Finset.disjoint_left.mp hAB hpa) (h ▸ hpb)
  have hT : ∀ e : Sym2 (Fin n), e ∈ (A ×ˢ B).image (fun p : Fin n × Fin n => s(p.1, p.2)) ↔
      e ∈ (SimpleGraph.between (A : Set (Fin n)) (B : Set (Fin n)) (⊤ : SimpleGraph (Fin n))).edgeSet := by
    intro e
    rw [← hset, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  rw [kst_code_linear_construction_finite_field_syndrome_eq_sum z _ _ hT]
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
    simp only [kst_code_linear_construction_finite_field_edge_weight_mk]
    rw [Finset.sum_mul_sum]
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_product] at hp hq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd (h1 ▸ hq.2) (Finset.disjoint_left.mp hAB hp.1)

/-- Linear graph-code construction via finite field multiplication (Lemma 4.2, arXiv:2610.35136). -/
theorem kst_code_linear_construction_finite_field
    (n s t r : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (w : Fin n → Fin r → ZMod 2)
    (hw : ∀ S : Finset (Fin n), (S.card = s ∨ S.card = t) → ∑ i ∈ S, w i ≠ 0) :
    ∃ C : Set (SimpleGraph (Fin n)),
      is_kst_code s t n C ∧
      is_binary_linear_graph_code n C ∧
      n.choose 2 - Nat.log 2 (Set.ncard C) ≤ r ∧
      (1 / 2 : ℝ) ^ r ≤ (Set.ncard C : ℝ) / (2 ^ (n.choose 2) : ℝ) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 r) := Fintype.ofFinite _
  have hr0 : r ≠ 0 := by omega
  let φ : (Fin r → ZMod 2) ≃ₗ[ZMod 2] GaloisField 2 r :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      exact (GaloisField.finrank 2 hr0).symm)
  let z : Fin n → GaloisField 2 r := fun i => φ (w i)
  have hz : ∀ S : Finset (Fin n), (S.card = s ∨ S.card = t) → ∑ i ∈ S, z i ≠ 0 := by
    intro S hS hsum0
    apply hw S hS
    have hmap : φ (∑ i ∈ S, w i) = ∑ i ∈ S, z i := by
      simp only [z]
      exact map_sum φ w S
    have h0 : φ (∑ i ∈ S, w i) = 0 := by rw [hmap]; exact hsum0
    exact φ.injective (by rw [h0, map_zero])
  let C : Set (SimpleGraph (Fin n)) := {G | kst_code_linear_construction_finite_field_syndrome z G = 0}
  have hCbot : (⊥ : SimpleGraph (Fin n)) ∈ C := by
    simp [C]
  have hCclos : ∀ G G' : SimpleGraph (Fin n), G ∈ C → G' ∈ C → symmDiff G G' ∈ C := by
    intro G G' hG hG'
    simp only [C, Set.mem_ofPred_eq] at hG hG' ⊢
    rw [kst_code_linear_construction_finite_field_syndrome_symmDiff, hG, hG', add_zero]
  let rep : GaloisField 2 r → SimpleGraph (Fin n) :=
    fun y => if h : ∃ G : SimpleGraph (Fin n),
      kst_code_linear_construction_finite_field_syndrome z G = y then h.choose else ⊥
  have hrep : ∀ (y : GaloisField 2 r)
      (hy : ∃ G : SimpleGraph (Fin n),
        kst_code_linear_construction_finite_field_syndrome z G = y),
      kst_code_linear_construction_finite_field_syndrome z (rep y) = y := by
    intro y hy
    simp only [rep]
    rw [dif_pos hy]
    exact hy.choose_spec
  have hmemC : ∀ G : SimpleGraph (Fin n),
      symmDiff G (rep (kst_code_linear_construction_finite_field_syndrome z G)) ∈ C := by
    intro G
    simp only [C, Set.mem_ofPred_eq]
    rw [kst_code_linear_construction_finite_field_syndrome_symmDiff,
      hrep (kst_code_linear_construction_finite_field_syndrome z G) ⟨G, rfl⟩]
    exact CharTwo.add_self_eq_zero _
  have hcancel : ∀ (X R : SimpleGraph (Fin n)), symmDiff (symmDiff X R) R = X := by
    intro X R
    rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
  have hinj : Function.Injective (fun G : SimpleGraph (Fin n) =>
      (kst_code_linear_construction_finite_field_syndrome z G,
        (⟨symmDiff G (rep (kst_code_linear_construction_finite_field_syndrome z G)),
          hmemC G⟩ : ↥C))) := by
    intro G1 G2 h
    have h1 : kst_code_linear_construction_finite_field_syndrome z G1
        = kst_code_linear_construction_finite_field_syndrome z G2 := congrArg Prod.fst h
    have h2 : symmDiff G1 (rep (kst_code_linear_construction_finite_field_syndrome z G1))
        = symmDiff G2 (rep (kst_code_linear_construction_finite_field_syndrome z G2)) :=
      congrArg (fun p : GaloisField 2 r × ↥C => ((p.2 : ↥C) : SimpleGraph (Fin n))) h
    rw [h1] at h2
    calc G1 = symmDiff (symmDiff G1 (rep (kst_code_linear_construction_finite_field_syndrome z G2)))
          (rep (kst_code_linear_construction_finite_field_syndrome z G2)) := (hcancel _ _).symm
      _ = symmDiff (symmDiff G2 (rep (kst_code_linear_construction_finite_field_syndrome z G2)))
          (rep (kst_code_linear_construction_finite_field_syndrome z G2)) := by rw [h2]
      _ = G2 := hcancel _ _
  have hcardG : Fintype.card (SimpleGraph (Fin n)) = 2 ^ (n.choose 2) := by
    rw [card_simpleGraph, Fintype.card_fin]
  have hcardF : Fintype.card (GaloisField 2 r) = 2 ^ r := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 r hr0]
  have hcardC : Fintype.card ↥C = Set.ncard C := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hmain : 2 ^ (n.choose 2) ≤ 2 ^ r * Set.ncard C := by
    have hle := Fintype.card_le_of_injective _ hinj
    rwa [Fintype.card_prod, hcardF, hcardC, hcardG] at hle
  have hCpos : 0 < Set.ncard C := by
    rw [Set.ncard_pos]
    exact ⟨⊥, hCbot⟩
  refine ⟨C, ?_, ⟨hCbot, hCclos⟩, ?_, ?_⟩
  · intro G G' hG hG' hne A B hAB hA hB hcontra
    simp only [C, Set.mem_ofPred_eq] at hG hG'
    have hzero : kst_code_linear_construction_finite_field_syndrome z (symmDiff G G') = 0 := by
      rw [kst_code_linear_construction_finite_field_syndrome_symmDiff, hG, hG', add_zero]
    rw [hcontra, kst_code_linear_construction_finite_field_syndrome_between z A B hAB] at hzero
    exact mul_ne_zero (hz A (Or.inl hA)) (hz B (Or.inr hB)) hzero
  · have hpow : 2 ^ (n.choose 2 - r) ≤ Set.ncard C := by
      by_cases h : r ≤ n.choose 2
      · have h2 : 2 ^ r * 2 ^ (n.choose 2 - r) ≤ 2 ^ r * Set.ncard C := by
          rw [← pow_add, Nat.add_sub_cancel' h]
          exact hmain
        exact Nat.le_of_mul_le_mul_left h2 (by positivity)
      · rw [Nat.sub_eq_zero_of_le (by omega : n.choose 2 ≤ r), pow_zero]
        omega
    have hlog : n.choose 2 - r ≤ Nat.log 2 (Set.ncard C) := by
      rw [Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (by omega : Set.ncard C ≠ 0)]
      exact hpow
    omega
  · have hmainR : (2 : ℝ) ^ (n.choose 2) ≤ (2 : ℝ) ^ r * (Set.ncard C : ℝ) := by
      exact_mod_cast hmain
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
      mul_comm (Set.ncard C : ℝ) ((2 : ℝ) ^ r)]
    exact hmainR
