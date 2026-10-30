import AFTD.Prelude
import AFTD.Kb.Tcs.Op639TransversalFourSingletonNonempty

/-!
# op_639_sum_triple_fibers_card_le_twelve

Topic: combinatorics   Node: 811077685cb4

Provenance: helper lemma. step towards op_639_intersecting_four_uniform_covering_four_card_le_forty_two

In a 4-uniform intersecting family with tau >= 4 and a transversal T of size 4, the sum of sizes of edges whose intersection with T has cardinality 3 is at most 12.
-/

lemma op_639_sum_triple_fibers_card_le_twelve_fiber_le_three
    {V : Type*} [DecidableEq V] (F : Finset (Finset V))
    (hunif : ∀ e ∈ F, e.card = 4)
    (hinter : (F : Set (Finset V)).Intersecting)
    (htau_ge : ∀ T : Finset V, T.card < 4 → ∃ e ∈ F, Disjoint e T)
    (T : Finset V) (hT : T.card = 4) (hT_trans : ∀ e ∈ F, ¬Disjoint e T)
    (S : Finset V) (hS : S ∈ T.powersetCard 3) :
    (F.filter (fun e => e ∩ T = S)).card ≤ 3 := by
  rw [Finset.mem_powersetCard] at hS
  have hcard_sdiff : (T \ S).card = 1 := by
    rw [Finset.card_sdiff_of_subset hS.1, hT, hS.2]
  obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hcard_sdiff
  have hx_in_T : x ∈ T := by
    have : x ∈ T \ S := by rw [hx_eq]; exact Finset.mem_singleton_self x
    exact (Finset.mem_sdiff.mp this).1
  have hx_not_in_S : x ∉ S := by
    have : x ∈ T \ S := by rw [hx_eq]; exact Finset.mem_singleton_self x
    exact (Finset.mem_sdiff.mp this).2
  obtain ⟨e0, he0_in_F, he0_inter⟩ :=
    op_639_transversal_four_singleton_nonempty F htau_ge T hT hT_trans x hx_in_T
  have he0_sdiff_card : (e0 \ T).card = 3 := by
    rw [← Finset.sdiff_inter_self_left e0 T, he0_inter]
    have hx_in_e0 : x ∈ e0 := by
      have : x ∈ e0 ∩ T := by rw [he0_inter]; exact Finset.mem_singleton_self x
      exact (Finset.mem_inter.mp this).1
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hx_in_e0)]
    rw [Finset.card_singleton, hunif e0 he0_in_F]
  let G := F.filter (fun e => e ∩ T = S)
  have hG_card : G.card ≤ ((e0 \ T).powersetCard 1).card := by
    apply Finset.card_le_card_of_injOn (fun e => e \ T)
    · intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      have he_in_F : e ∈ F := he.1
      have he_inter : e ∩ T = S := he.2
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      have he_sdiff_card : (e \ T).card = 1 := by
        rw [← Finset.sdiff_inter_self_left e T]
        rw [Finset.card_sdiff_of_subset (Finset.inter_subset_left : e ∩ T ⊆ e)]
        rw [he_inter, hunif e he_in_F, hS.2]
      dsimp only
      refine ⟨?_, he_sdiff_card⟩
      have h_inter_nonempty : (e ∩ e0).Nonempty := by
        have h_not_disj := hinter (Finset.mem_coe.mpr he_in_F) (Finset.mem_coe.mpr he0_in_F)
        exact Finset.not_disjoint_iff_nonempty_inter.mp h_not_disj
      have h_inter_sub_sdiff : e ∩ e0 ⊆ e \ T := by
        intro z hz
        rw [Finset.mem_inter] at hz
        rw [Finset.mem_sdiff]
        refine ⟨hz.1, fun hzT => ?_⟩
        have hz_in_inter : z ∈ e ∩ T := Finset.mem_inter.mpr ⟨hz.1, hzT⟩
        rw [he_inter] at hz_in_inter
        have hz_in_e0T : z ∈ e0 ∩ T := Finset.mem_inter.mpr ⟨hz.2, hzT⟩
        rw [he0_inter, Finset.mem_singleton] at hz_in_e0T
        subst hz_in_e0T
        exact hx_not_in_S hz_in_inter
      have h_inter_sub_e0sdiff : e ∩ e0 ⊆ e0 \ T := by
        intro z hz
        rw [Finset.mem_inter] at hz
        rw [Finset.mem_sdiff]
        refine ⟨hz.2, fun hzT => ?_⟩
        have hz_in_inter : z ∈ e ∩ T := Finset.mem_inter.mpr ⟨hz.1, hzT⟩
        rw [he_inter] at hz_in_inter
        have hz_in_e0T : z ∈ e0 ∩ T := Finset.mem_inter.mpr ⟨hz.2, hzT⟩
        rw [he0_inter, Finset.mem_singleton] at hz_in_e0T
        subst hz_in_e0T
        exact hx_not_in_S hz_in_inter
      have h_eq : e ∩ e0 = e \ T := by
        have h1 : 0 < (e ∩ e0).card := Finset.card_pos.mpr h_inter_nonempty
        have h2 : (e ∩ e0).card ≤ (e \ T).card := Finset.card_le_card h_inter_sub_sdiff
        rw [he_sdiff_card] at h2
        have h3 : (e ∩ e0).card = (e \ T).card := by omega
        exact Finset.eq_of_subset_of_card_le h_inter_sub_sdiff (by omega)
      rw [← h_eq]
      exact h_inter_sub_e0sdiff
    · intro e1 he1 e2 he2 heq
      rw [Finset.mem_coe, Finset.mem_filter] at he1 he2
      have he1_recon : e1 = S ∪ (e1 \ T) := by
        rw [Finset.union_comm, ← he1.2, Finset.sdiff_union_inter]
      have he2_recon : e2 = S ∪ (e2 \ T) := by
        rw [Finset.union_comm, ← he2.2, Finset.sdiff_union_inter]
      dsimp at heq
      rw [he1_recon, he2_recon, heq]
  rw [Finset.card_powersetCard, Nat.choose_one_right, he0_sdiff_card] at hG_card
  exact hG_card

/-- The sum of sizes of all 4 triple fibers is at most 12. -/
theorem op_639_sum_triple_fibers_card_le_twelve
    {V : Type*} [DecidableEq V] (F : Finset (Finset V))
    (hunif : ∀ e ∈ F, e.card = 4)
    (hinter : (F : Set (Finset V)).Intersecting)
    (htau_ge : ∀ T : Finset V, T.card < 4 → ∃ e ∈ F, Disjoint e T)
    (T : Finset V) (hT : T.card = 4) (hT_trans : ∀ e ∈ F, ¬Disjoint e T) :
    (∑ S ∈ T.powersetCard 3, (F.filter (fun e => e ∩ T = S)).card) ≤ 12 := by
  have h_le_three : ∀ S ∈ T.powersetCard 3, (F.filter (fun e => e ∩ T = S)).card ≤ 3 := by
    intro S hS
    exact op_639_sum_triple_fibers_card_le_twelve_fiber_le_three F hunif hinter htau_ge T hT hT_trans S hS
  have h_sum := Finset.sum_le_card_nsmul (T.powersetCard 3) (fun S => (F.filter (fun e => e ∩ T = S)).card) 3 h_le_three
  have h_choose : (T.powersetCard 3).card = 4 := by
    rw [Finset.card_powersetCard, hT]
    decide
  rw [nsmul_eq_mul, h_choose] at h_sum
  omega
