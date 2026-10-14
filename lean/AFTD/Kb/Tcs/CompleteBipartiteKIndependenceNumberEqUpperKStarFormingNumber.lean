import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphKIndependenceNumber
import AFTD.Kb.Tcs.SimpleGraphUpperKStarFormingNumber
import AFTD.Kb.Tcs.SimpleGraphIsKStarFormingMono
import AFTD.Kb.Tcs.SimpleGraphIsKStarForming
import AFTD.Kb.Tcs.SimpleGraphIsKIndependentIff
import AFTD.Kb.Tcs.SimpleGraphIsKStarFormingIff
import AFTD.Kb.Tcs.SimpleGraphIsMinimalKStarForming
import AFTD.Kb.Tcs.SimpleGraphIsKIndependent

/-!
# complete_bipartite_k_independence_number_eq_upper_k_star_forming_number

Topic: graphs   Node: d763d74d4c39

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Theorem 3.2.

For k ≥ 2 and a, b ≥ k, the complete bipartite graph K_{a,b} has β_k(K_{a,b}) = SF_k(K_{a,b}) = max{a, b, 2k − 2}.
-/

theorem complete_bipartite_k_independence_number_eq_upper_k_star_forming_number
    (k a b : ℕ) (hk : 2 ≤ k) (ha : k ≤ a) (hb : k ≤ b) :
    simple_graph_k_independence_number (completeBipartiteGraph (Fin a) (Fin b)) k =
        max a (max b (2 * k - 2)) ∧
      simple_graph_upper_k_star_forming_number (completeBipartiteGraph (Fin a) (Fin b)) k =
        max a (max b (2 * k - 2)) := open Finset in by
  classical
  set K := completeBipartiteGraph (Fin a) (Fin b) with hK
  unfold simple_graph_k_independence_number simple_graph_upper_k_star_forming_number
  -- neighbourhoods inside a set, in terms of the two sides
  have hNl : ∀ (S : Finset (Fin a ⊕ Fin b)) i, (S.filter (K.Adj (Sum.inl i))).card = S.toRight.card := by
    intro S i
    have : S.filter (K.Adj (Sum.inl i)) = S.toRight.map Function.Embedding.inr := by
      ext w
      rcases w with w | w <;> simp [hK]
    rw [this, card_map]
  have hNr : ∀ (S : Finset (Fin a ⊕ Fin b)) j, (S.filter (K.Adj (Sum.inr j))).card = S.toLeft.card := by
    intro S j
    have : S.filter (K.Adj (Sum.inr j)) = S.toLeft.map Function.Embedding.inl := by
      ext w
      rcases w with w | w <;> simp [hK]
    rw [this, card_map]
  have hcard : ∀ S : Finset (Fin a ⊕ Fin b), S.card = S.toLeft.card + S.toRight.card :=
    fun S => card_toLeft_add_card_toRight.symm
  have hxa : ∀ S : Finset (Fin a ⊕ Fin b), S.toLeft.card ≤ a := fun S =>
    (card_le_univ _).trans (by simp)
  have hyb : ∀ S : Finset (Fin a ⊕ Fin b), S.toRight.card ≤ b := fun S =>
    (card_le_univ _).trans (by simp)
  have hxa' : ∀ S : Finset (Fin a ⊕ Fin b), S.toLeft.card = a ↔ ∀ i, Sum.inl i ∈ S := by
    intro S
    constructor
    · intro h i
      have : S.toLeft = univ := eq_univ_of_card _ (by simpa using h)
      rw [← mem_toLeft, this]
      exact mem_univ i
    · intro h
      have : S.toLeft = univ := eq_univ_of_forall (fun i => mem_toLeft.2 (h i))
      rw [this]
      simp
  have hyb' : ∀ S : Finset (Fin a ⊕ Fin b), S.toRight.card = b ↔ ∀ j, Sum.inr j ∈ S := by
    intro S
    constructor
    · intro h j
      have : S.toRight = univ := eq_univ_of_card _ (by simpa using h)
      rw [← mem_toRight, this]
      exact mem_univ j
    · intro h
      have : S.toRight = univ := eq_univ_of_forall (fun j => mem_toRight.2 (h j))
      rw [this]
      simp
  have hx0 : ∀ S : Finset (Fin a ⊕ Fin b), S.toLeft.card = 0 ↔ ∀ i, Sum.inl i ∉ S := by
    intro S
    rw [card_eq_zero, eq_empty_iff_forall_notMem]
    simp
  have hy0 : ∀ S : Finset (Fin a ⊕ Fin b), S.toRight.card = 0 ↔ ∀ j, Sum.inr j ∉ S := by
    intro S
    rw [card_eq_zero, eq_empty_iff_forall_notMem]
    simp
  -- k-independence and star-forming in terms of the counts
  have hind : ∀ S : Finset (Fin a ⊕ Fin b), simple_graph_is_k_independent K k S ↔
      (S.toLeft.card = 0 ∨ S.toRight.card < k) ∧ (S.toRight.card = 0 ∨ S.toLeft.card < k) := by
    intro S
    rw [simple_graph_is_k_independent_iff]
    constructor
    · intro h
      constructor
      · by_cases h0 : S.toLeft.card = 0
        · exact Or.inl h0
        · right
          obtain ⟨i, hi⟩ : ∃ i, Sum.inl i ∈ S := by
            by_contra hn; push_neg at hn; exact h0 ((hx0 S).2 hn)
          have := h _ hi
          rwa [hNl] at this
      · by_cases h0 : S.toRight.card = 0
        · exact Or.inl h0
        · right
          obtain ⟨j, hj⟩ : ∃ j, Sum.inr j ∈ S := by
            by_contra hn; push_neg at hn; exact h0 ((hy0 S).2 hn)
          have := h _ hj
          rwa [hNr] at this
    · rintro ⟨h1, h2⟩ v hv
      rcases v with i | j
      · rw [hNl]
        exact h1.resolve_left (fun h => (hx0 S).1 h i hv)
      · rw [hNr]
        exact h2.resolve_left (fun h => (hy0 S).1 h j hv)
  have hsf : ∀ S : Finset (Fin a ⊕ Fin b), simple_graph_is_k_star_forming K k S ↔
      (S.toLeft.card = a ∨ k ≤ S.toRight.card ∨ (1 ≤ S.toRight.card ∧ k - 1 ≤ S.toLeft.card)) ∧
      (S.toRight.card = b ∨ k ≤ S.toLeft.card ∨ (1 ≤ S.toLeft.card ∧ k - 1 ≤ S.toRight.card)) := by
    intro S
    rw [simple_graph_is_k_star_forming_iff K k (by omega)]
    constructor
    · intro h
      constructor
      · by_cases hx : S.toLeft.card = a
        · exact Or.inl hx
        · right
          obtain ⟨i, hi⟩ : ∃ i, Sum.inl i ∉ S := by
            by_contra hn; push_neg at hn; exact hx ((hxa' S).2 hn)
          rcases h _ hi with h1 | ⟨u, huS, hvu, h2⟩
          · left; rwa [hNl] at h1
          · right
            rcases u with u | u
            · simp [hK] at hvu
            · rw [hNr] at h2
              refine ⟨?_, h2⟩
              rw [Nat.one_le_iff_ne_zero]
              exact fun h0 => (hy0 S).1 h0 u huS
      · by_cases hy : S.toRight.card = b
        · exact Or.inl hy
        · right
          obtain ⟨j, hj⟩ : ∃ j, Sum.inr j ∉ S := by
            by_contra hn; push_neg at hn; exact hy ((hyb' S).2 hn)
          rcases h _ hj with h1 | ⟨u, huS, hvu, h2⟩
          · left; rwa [hNr] at h1
          · right
            rcases u with u | u
            · rw [hNl] at h2
              refine ⟨?_, h2⟩
              rw [Nat.one_le_iff_ne_zero]
              exact fun h0 => (hx0 S).1 h0 u huS
            · simp [hK] at hvu
    · rintro ⟨h1, h2⟩ v hv
      rcases v with i | j
      · have hx : S.toLeft.card ≠ a := fun h => hv ((hxa' S).1 h i)
        rcases h1.resolve_left hx with h1 | ⟨hy1, hx1⟩
        · left; rwa [hNl]
        · right
          obtain ⟨j, hj⟩ : ∃ j, Sum.inr j ∈ S := by
            by_contra hn; push_neg at hn; have := (hy0 S).2 hn; omega
          exact ⟨Sum.inr j, hj, by simp [hK], by rwa [hNr]⟩
      · have hy : S.toRight.card ≠ b := fun h => hv ((hyb' S).1 h j)
        rcases h2.resolve_left hy with h2 | ⟨hx1, hy1⟩
        · left; rwa [hNr]
        · right
          obtain ⟨i, hi⟩ : ∃ i, Sum.inl i ∈ S := by
            by_contra hn; push_neg at hn; have := (hx0 S).2 hn; omega
          exact ⟨Sum.inl i, hi, by simp [hK], by rwa [hNl]⟩
  have hmin : ∀ S : Finset (Fin a ⊕ Fin b), simple_graph_is_minimal_k_star_forming K k S →
      S.card ≤ max a (max b (2 * k - 2)) := by
    rintro S ⟨hS, hm⟩
    have hS' := (hsf S).1 hS
    have hl : 1 ≤ S.toLeft.card → ¬ ((S.toLeft.card - 1 = a ∨ k ≤ S.toRight.card ∨
        (1 ≤ S.toRight.card ∧ k - 1 ≤ S.toLeft.card - 1)) ∧
        (S.toRight.card = b ∨ k ≤ S.toLeft.card - 1 ∨
          (1 ≤ S.toLeft.card - 1 ∧ k - 1 ≤ S.toRight.card))) := by
      intro h1 hc
      obtain ⟨i, hi⟩ : ∃ i, Sum.inl i ∈ S := by
        by_contra hn; push_neg at hn; have := (hx0 S).2 hn; omega
      have e1 : (S.erase (Sum.inl i)).toLeft.card = S.toLeft.card - 1 := by
        have : (S.erase (Sum.inl i)).toLeft = S.toLeft.erase i := by
          ext j; simp
        rw [this, card_erase_of_mem (mem_toLeft.2 hi)]
      have e2 : (S.erase (Sum.inl i)).toRight = S.toRight := by
        ext j; simp
      apply hm _ (erase_ssubset hi)
      rw [hsf, e1, e2]
      exact hc
    have hr : 1 ≤ S.toRight.card → ¬ ((S.toLeft.card = a ∨ k ≤ S.toRight.card - 1 ∨
        (1 ≤ S.toRight.card - 1 ∧ k - 1 ≤ S.toLeft.card)) ∧
        (S.toRight.card - 1 = b ∨ k ≤ S.toLeft.card ∨
          (1 ≤ S.toLeft.card ∧ k - 1 ≤ S.toRight.card - 1))) := by
      intro h1 hc
      obtain ⟨j, hj⟩ : ∃ j, Sum.inr j ∈ S := by
        by_contra hn; push_neg at hn; have := (hy0 S).2 hn; omega
      have e1 : (S.erase (Sum.inr j)).toRight.card = S.toRight.card - 1 := by
        have : (S.erase (Sum.inr j)).toRight = S.toRight.erase j := by
          ext i; simp
        rw [this, card_erase_of_mem (mem_toRight.2 hj)]
      have e2 : (S.erase (Sum.inr j)).toLeft = S.toLeft := by
        ext i; simp
      apply hm _ (erase_ssubset hj)
      rw [hsf, e1, e2]
      exact hc
    have := hxa S
    have := hyb S
    rw [hcard]
    omega
  -- sets with prescribed counts
  have hmk : ∀ x y, x ≤ a → y ≤ b → ∃ S : Finset (Fin a ⊕ Fin b),
      S.toLeft.card = x ∧ S.toRight.card = y := by
    intro x y hx hy
    refine ⟨(univ.map (Fin.castLEEmb hx)).disjSum (univ.map (Fin.castLEEmb hy)), ?_, ?_⟩ <;> simp
  have hbddI : BddAbove {n | ∃ I : Finset (Fin a ⊕ Fin b),
      simple_graph_is_k_independent K k I ∧ I.card = n} :=
    ⟨a + b, fun n ⟨I, _, hn⟩ => hn ▸ (card_le_univ I).trans (by simp)⟩
  have hbddS : BddAbove {n | ∃ S : Finset (Fin a ⊕ Fin b),
      simple_graph_is_minimal_k_star_forming K k S ∧ S.card = n} :=
    ⟨a + b, fun n ⟨S, _, hn⟩ => hn ▸ (card_le_univ S).trans (by simp)⟩
  -- the three extremal count pairs
  have hpairs : ∃ x y, x ≤ a ∧ y ≤ b ∧ x + y = max a (max b (2 * k - 2)) ∧
      (x = 0 ∨ y < k) ∧ (y = 0 ∨ x < k) ∧
      ((x = a ∨ k ≤ y ∨ (1 ≤ y ∧ k - 1 ≤ x)) ∧ (y = b ∨ k ≤ x ∨ (1 ≤ x ∧ k - 1 ≤ y))) ∧
      (1 ≤ x → ¬ ((x - 1 = a ∨ k ≤ y ∨ (1 ≤ y ∧ k - 1 ≤ x - 1)) ∧
        (y = b ∨ k ≤ x - 1 ∨ (1 ≤ x - 1 ∧ k - 1 ≤ y)))) ∧
      (1 ≤ y → ¬ ((x = a ∨ k ≤ y - 1 ∨ (1 ≤ y - 1 ∧ k - 1 ≤ x)) ∧
        (y - 1 = b ∨ k ≤ x ∨ (1 ≤ x ∧ k - 1 ≤ y - 1)))) := by
    by_cases h1 : b ≤ a ∧ 2 * k - 2 ≤ a
    · exact ⟨a, 0, le_rfl, Nat.zero_le _, by omega, by omega, by omega, by omega, by omega,
        by omega⟩
    · by_cases h2 : a ≤ b ∧ 2 * k - 2 ≤ b
      · exact ⟨0, b, Nat.zero_le _, le_rfl, by omega, by omega, by omega, by omega, by omega,
          by omega⟩
      · exact ⟨k - 1, k - 1, by omega, by omega, by omega, by omega, by omega, by omega,
          by omega, by omega⟩
  obtain ⟨x, y, hx, hy, hxy, hi1, hi2, hs1, hs2, hs3⟩ := hpairs
  obtain ⟨S₀, hS₀x, hS₀y⟩ := hmk x y hx hy
  constructor
  · apply le_antisymm
    · refine csSup_le (Set.nonempty_of_mem (x := 0) ⟨∅, fun v hv => by simp at hv, rfl⟩) ?_
      rintro n ⟨I, hI, rfl⟩
      have := (hind I).1 hI
      have := hxa I
      have := hyb I
      rw [hcard]
      omega
    · apply le_csSup hbddI
      refine ⟨S₀, (hind S₀).2 ?_, ?_⟩
      · rw [hS₀x, hS₀y]; exact ⟨hi1, hi2⟩
      · rw [hcard, hS₀x, hS₀y, hxy]
  · have hmem : max a (max b (2 * k - 2)) ∈ {n | ∃ S : Finset (Fin a ⊕ Fin b),
        simple_graph_is_minimal_k_star_forming K k S ∧ S.card = n} := by
      refine ⟨S₀, ⟨(hsf S₀).2 (by rw [hS₀x, hS₀y]; exact hs1), ?_⟩, by rw [hcard, hS₀x, hS₀y, hxy]⟩
      intro T hT hTsf
      obtain ⟨s, hsS, hsT⟩ := exists_of_ssubset hT
      have hsub : T ⊆ S₀.erase s := fun t ht => mem_erase.2 ⟨fun h => hsT (h ▸ ht), hT.1 ht⟩
      have h2 := (hsf _).1 (simple_graph_is_k_star_forming_mono K k hsub hTsf)
      rcases s with i | j
      · have e1 : (S₀.erase (Sum.inl i)).toLeft.card = x - 1 := by
          have : (S₀.erase (Sum.inl i)).toLeft = S₀.toLeft.erase i := by
            ext j; simp
          rw [this, card_erase_of_mem (mem_toLeft.2 hsS), hS₀x]
        have e2 : (S₀.erase (Sum.inl i)).toRight = S₀.toRight := by
          ext j; simp
        have hx1 : 1 ≤ x := by
          rw [← hS₀x]; exact card_pos.2 ⟨i, mem_toLeft.2 hsS⟩
        rw [e1, e2, hS₀y] at h2
        exact hs2 hx1 h2
      · have e1 : (S₀.erase (Sum.inr j)).toRight.card = y - 1 := by
          have : (S₀.erase (Sum.inr j)).toRight = S₀.toRight.erase j := by
            ext i; simp
          rw [this, card_erase_of_mem (mem_toRight.2 hsS), hS₀y]
        have e2 : (S₀.erase (Sum.inr j)).toLeft = S₀.toLeft := by
          ext i; simp
        have hy1 : 1 ≤ y := by
          rw [← hS₀y]; exact card_pos.2 ⟨j, mem_toRight.2 hsS⟩
        rw [e1, e2, hS₀x] at h2
        exact hs3 hy1 h2
    apply le_antisymm
    · refine csSup_le ⟨_, hmem⟩ ?_
      rintro n ⟨S, hS, rfl⟩
      exact hmin S hS
    · exact le_csSup hbddS hmem
