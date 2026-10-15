import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsChainGraph
import AFTD.Kb.Tcs.SimpleGraphKIndependenceNumber
import AFTD.Kb.Tcs.SimpleGraphUpperKStarFormingNumber
import AFTD.Kb.Tcs.SimpleGraphKIndependenceNumberLeUpperKStarFormingNumber
import AFTD.Kb.Tcs.SimpleGraphIsKStarFormingIff
import AFTD.Kb.Tcs.SimpleGraphIsMinimalKStarForming
import AFTD.Kb.Tcs.SimpleGraphIsKIndependent
import AFTD.Kb.Tcs.SimpleGraphIsKStarForming
import AFTD.Kb.Tcs.SimpleGraphIsKIndependentIff

/-!
# chain_graph_two_independence_number_eq_upper_two_star_forming_number

Topic: graphs   Node: e98e598110d5

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Theorem 6.2 (the case k = 2 of the question whose case k ≥ 3 is Conjecture 6.4, OP-217).

For every finite chain graph G, the dissociation number β₂(G) equals the upper 2-star-forming number SF₂(G).
-/

open Finset

lemma chain_graph_two_independence_number_eq_upper_two_star_forming_number_filter_adj_card_pos_iff
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u : V) :
    1 ≤ (S.filter (G.Adj u)).card ↔ ∃ w ∈ S, G.Adj u w := by
  rw [Nat.succ_le_iff, card_pos, Finset.Nonempty]
  simp

lemma chain_graph_two_independence_number_eq_upper_two_star_forming_number_star_forming_two_erase_of_subset
    {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V)
    (h_bip : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (S : Finset V) (hS : simple_graph_is_k_star_forming G 2 S)
    (a : V) (haS : a ∈ S) (haA : a ∈ A)
    (b₁ b₂ : V) (hb₁S : b₁ ∈ S) (hb₂S : b₂ ∈ S) (hne : b₁ ≠ b₂)
    (hadj1 : G.Adj a b₁) (hadj2 : G.Adj a b₂)
    (hsub : G.neighborSet b₁ ⊆ G.neighborSet b₂) :
    simple_graph_is_k_star_forming G 2 (S.erase b₁) := by
  have hb₁nA : b₁ ∉ A := by
    have := (h_bip a b₁ hadj1).mp haA
    exact this
  have h_anea : a ≠ b₁ := by
    rintro rfl
    exact hb₁nA haA
  have h_a_in : a ∈ S.erase b₁ := mem_erase.mpr ⟨h_anea, haS⟩
  have h_b2_in : b₂ ∈ S.erase b₁ := mem_erase.mpr ⟨hne.symm, hb₂S⟩
  rw [simple_graph_is_k_star_forming_iff G 2 (by omega)] at hS ⊢
  intro v hv
  by_cases hv_b1 : v = b₁
  · rw [hv_b1]
    right
    refine ⟨a, h_a_in, hadj1.symm, ?_⟩
    have : 2 - 1 = 1 := rfl
    rw [this, chain_graph_two_independence_number_eq_upper_two_star_forming_number_filter_adj_card_pos_iff]
    exact ⟨b₂, h_b2_in, hadj2⟩
  · have hv_not_S : v ∉ S := by
      intro h
      have : v ∈ S.erase b₁ := mem_erase.mpr ⟨hv_b1, h⟩
      exact hv this
    rcases hS v hv_not_S with h1 | ⟨u, huS, hadj_vu, h2⟩
    · by_cases hvA : v ∈ A
      · by_cases hadj_vb1 : G.Adj v b₁
        · right
          have hadj_vb2 : G.Adj v b₂ := by
            have : v ∈ G.neighborSet b₁ := hadj_vb1.symm
            exact (hsub this).symm
          refine ⟨b₂, h_b2_in, hadj_vb2, ?_⟩
          have : 2 - 1 = 1 := rfl
          rw [this, chain_graph_two_independence_number_eq_upper_two_star_forming_number_filter_adj_card_pos_iff]
          exact ⟨a, h_a_in, hadj2.symm⟩
        · left
          have heq : (S.erase b₁).filter (G.Adj v) = S.filter (G.Adj v) := by
            ext w
            simp only [mem_filter, mem_erase]
            constructor
            · rintro ⟨⟨-, hwS⟩, hwadj⟩; exact ⟨hwS, hwadj⟩
            · rintro ⟨hwS, hwadj⟩
              refine ⟨⟨?_, hwS⟩, hwadj⟩
              rintro rfl
              exact hadj_vb1 hwadj
          rw [heq]
          exact h1
      · left
        have heq : (S.erase b₁).filter (G.Adj v) = S.filter (G.Adj v) := by
          ext w
          simp only [mem_filter, mem_erase]
          constructor
          · rintro ⟨⟨-, hwS⟩, hwadj⟩; exact ⟨hwS, hwadj⟩
          · rintro ⟨hwS, hwadj⟩
            refine ⟨⟨?_, hwS⟩, hwadj⟩
            rintro rfl
            have hwA : w ∈ A := by
              have := (h_bip v w hwadj).not.mp hvA
              exact not_not.mp this
            exact hb₁nA hwA
        rw [heq]
        exact h1
    · by_cases hu_b1 : u = b₁
      · right
        have hadj_vb2 : G.Adj v b₂ := by
          have hadj_vb1 : G.Adj v b₁ := hu_b1 ▸ hadj_vu
          have : v ∈ G.neighborSet b₁ := hadj_vb1.symm
          exact (hsub this).symm
        refine ⟨b₂, h_b2_in, hadj_vb2, ?_⟩
        have : 2 - 1 = 1 := rfl
        rw [this, chain_graph_two_independence_number_eq_upper_two_star_forming_number_filter_adj_card_pos_iff]
        exact ⟨a, h_a_in, hadj2.symm⟩
      · right
        have hu_in : u ∈ S.erase b₁ := mem_erase.mpr ⟨hu_b1, huS⟩
        refine ⟨u, hu_in, hadj_vu, ?_⟩
        have : 2 - 1 = 1 := rfl
        rw [this] at h2 ⊢
        rw [chain_graph_two_independence_number_eq_upper_two_star_forming_number_filter_adj_card_pos_iff] at h2 ⊢
        rcases h2 with ⟨w, hwS, hadj_uw⟩
        by_cases hw_b1 : w = b₁
        · have hadj_ub2 : G.Adj u b₂ := by
            have hadj_ub1 : G.Adj u b₁ := hw_b1 ▸ hadj_uw
            have : u ∈ G.neighborSet b₁ := hadj_ub1.symm
            exact (hsub this).symm
          exact ⟨b₂, h_b2_in, hadj_ub2⟩
        · exact ⟨w, mem_erase.mpr ⟨hw_b1, hwS⟩, hadj_uw⟩

lemma chain_graph_two_independence_number_eq_upper_two_star_forming_number_chain_graph_symm
    {V : Type*} (G : SimpleGraph V) (A : Set V)
    (hG : simple_graph_is_chain_graph G A) :
    simple_graph_is_chain_graph G (Aᶜ) := by
  classical
  constructor
  · intro u v hadj
    have := hG.1 v u hadj.symm
    simp only [Set.mem_compl_iff]
    tauto
  · intro b₁ hb₁ b₂ hb₂
    simp only [Set.mem_compl_iff] at hb₁ hb₂
    have chain_graph_B_ordered (b₁ b₂ : V) (hb₁ : b₁ ∉ A) (hb₂ : b₂ ∉ A) :
        G.neighborSet b₁ ⊆ G.neighborSet b₂ ∨ G.neighborSet b₂ ⊆ G.neighborSet b₁ := by
      by_contra h
      rw [not_or, Set.not_subset, Set.not_subset] at h
      rcases h with ⟨⟨a₁, ha₁b₁, ha₁nb₂⟩, ⟨a₂, ha₂b₂, ha₂nb₁⟩⟩
      have hadj1 : G.Adj b₁ a₁ := ha₁b₁
      have hadj2 : G.Adj b₂ a₂ := ha₂b₂
      have ha₁A : a₁ ∈ A := by
        have := (hG.1 b₁ a₁ hadj1).not.mp hb₁
        exact not_not.mp this
      have ha₂A : a₂ ∈ A := by
        have := (hG.1 b₂ a₂ hadj2).not.mp hb₂
        exact not_not.mp this
      have hb₁a₁ : b₁ ∈ G.neighborSet a₁ := hadj1.symm
      have hb₂na₁ : b₂ ∉ G.neighborSet a₁ := fun h => ha₁nb₂ h.symm
      have hb₂a₂ : b₂ ∈ G.neighborSet a₂ := hadj2.symm
      have hb₁na₂ : b₁ ∉ G.neighborSet a₂ := fun h => ha₂nb₁ h.symm
      rcases hG.2 a₁ ha₁A a₂ ha₂A with h1 | h2
      · exact hb₁na₂ (h1 hb₁a₁)
      · exact hb₂na₁ (h2 hb₂a₂)
    exact chain_graph_B_ordered b₁ b₂ hb₁ hb₂

lemma chain_graph_two_independence_number_eq_upper_two_star_forming_number_card_filter_adj_lt_two_of_mem_A
    {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V)
    (hG : simple_graph_is_chain_graph G A)
    (S : Finset V) (hS : simple_graph_is_minimal_k_star_forming G 2 S)
    (a : V) (haS : a ∈ S) (haA : a ∈ A) :
    (S.filter (G.Adj a)).card < 2 := by
  by_contra! hge
  obtain ⟨b₁, hb₁, b₂, hb₂, hne⟩ := Finset.one_lt_card.mp hge
  rw [mem_filter] at hb₁ hb₂
  rcases hb₁ with ⟨hb₁S, hadj1⟩
  rcases hb₂ with ⟨hb₂S, hadj2⟩
  have hb₁nA : b₁ ∉ A := (hG.1 a b₁ hadj1).mp haA
  have hb₂nA : b₂ ∉ A := (hG.1 a b₂ hadj2).mp haA
  have hsymm := chain_graph_two_independence_number_eq_upper_two_star_forming_number_chain_graph_symm G A hG
  rcases hsymm.2 b₁ hb₁nA b₂ hb₂nA with hsub | hsub
  · have h_erase_sf : simple_graph_is_k_star_forming G 2 (S.erase b₁) :=
      chain_graph_two_independence_number_eq_upper_two_star_forming_number_star_forming_two_erase_of_subset
        G A hG.1 S hS.1 a haS haA b₁ b₂ hb₁S hb₂S hne hadj1 hadj2 hsub
    have h_ssub : S.erase b₁ ⊂ S := erase_ssubset hb₁S
    exact hS.2 _ h_ssub h_erase_sf
  · have h_erase_sf : simple_graph_is_k_star_forming G 2 (S.erase b₂) :=
      chain_graph_two_independence_number_eq_upper_two_star_forming_number_star_forming_two_erase_of_subset
        G A hG.1 S hS.1 a haS haA b₂ b₁ hb₂S hb₁S hne.symm hadj2 hadj1 hsub
    have h_ssub : S.erase b₂ ⊂ S := erase_ssubset hb₂S
    exact hS.2 _ h_ssub h_erase_sf

lemma chain_graph_two_independence_number_eq_upper_two_star_forming_number_minimal_star_forming_two_is_two_independent
    {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Set V)
    (hG : simple_graph_is_chain_graph G A)
    (S : Finset V) (hS : simple_graph_is_minimal_k_star_forming G 2 S) :
    simple_graph_is_k_independent G 2 S := by
  rw [simple_graph_is_k_independent_iff]
  intro v hv
  by_cases hvA : v ∈ A
  · exact chain_graph_two_independence_number_eq_upper_two_star_forming_number_card_filter_adj_lt_two_of_mem_A
      G A hG S hS v hv hvA
  · have hsymm := chain_graph_two_independence_number_eq_upper_two_star_forming_number_chain_graph_symm G A hG
    exact chain_graph_two_independence_number_eq_upper_two_star_forming_number_card_filter_adj_lt_two_of_mem_A
      G (Aᶜ) hsymm S hS v hv hvA

theorem chain_graph_two_independence_number_eq_upper_two_star_forming_number {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (hG : simple_graph_is_chain_graph G A) :
    simple_graph_k_independence_number G 2 = simple_graph_upper_k_star_forming_number G 2 := by
  classical
  apply le_antisymm
  · exact simple_graph_k_independence_number_le_upper_k_star_forming_number G 2
  · unfold simple_graph_upper_k_star_forming_number
    by_cases hne : {n | ∃ S : Finset V, simple_graph_is_minimal_k_star_forming G 2 S ∧ S.card = n}.Nonempty
    · apply csSup_le hne
      rintro n ⟨S, hS, rfl⟩
      have hS_ind :=
        chain_graph_two_independence_number_eq_upper_two_star_forming_number_minimal_star_forming_two_is_two_independent
          G A hG S hS
      have hbdd : BddAbove {m | ∃ I : Finset V, simple_graph_is_k_independent G 2 I ∧ I.card = m} := by
        refine ⟨Fintype.card V, ?_⟩
        rintro m ⟨I, -, rfl⟩
        exact card_le_univ I
      have hmem : S.card ∈ {m | ∃ I : Finset V, simple_graph_is_k_independent G 2 I ∧ I.card = m} :=
        ⟨S, hS_ind, rfl⟩
      exact le_csSup hbdd hmem
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, csSup_empty]
      exact Nat.zero_le _
