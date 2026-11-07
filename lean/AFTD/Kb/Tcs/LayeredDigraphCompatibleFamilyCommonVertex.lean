import AFTD.Prelude
import AFTD.Kb.Tcs.FinIntervalsIntersectionNonemptyOfPairwiseInter
import AFTD.Kb.Tcs.IsLayeredDag
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# layered_digraph_compatible_family_common_vertex

Topic: graphs   Node: f853fca5e16d

Provenance: formalization of a published result. Source: scout/2611-07043-polynomial-lower-bounds-for-steiner-shortcuts-via-test-func.md:393, arXiv:2611.07043 Lemma 2.3

Let G = (V, E) be a directed graph on a vertex type V, let L be a positive natural number (0 < L), and let layer : V → ℕ be a layer assignment such that G is a layered DAG with respect to layer (is_layered_dag G layer, meaning every directed edge connects a vertex in layer i to a vertex in layer i + 1). Let paths be a family of paths in G from layer 0 to layer L - 1, where each path P ∈ paths is represented as a function P : Fin L → V satisfying layer (P i) = i.val for all i and (P i, P j) ∈ E whenever j = i + 1. Assume property (P1): for each P ∈ paths, P is the unique directed path in G between its start s(P) = P ⟨0, hL⟩ and its end t(P) = P ⟨L - 1, ...⟩, so that any function Q : Fin L → V satisfying layer (Q i) = i.val for all i and (Q i, Q j) ∈ E for j = i + 1 with Q ⟨0, hL⟩ = P ⟨0, hL⟩ and Q ⟨L - 1, ...⟩ = P ⟨L - 1, ...⟩ satisfies Q = P. Assume property (P2): for each compatible pair P, Q ∈ paths (meaning s(P) reaches t(Q) and s(Q) reaches t(P) via a directed walk in G), P and Q share a common vertex (there exists v ∈ V in both the range of P and the range of Q). Then for every nonempty family F ⊆ paths that is compatible (meaning s(P) reaches t(Q) via a directed walk in G for all P, Q ∈ F), there exists a single vertex v ∈ V contained in every path of F (v is in the range of every P ∈ F).
-/

open Classical in
lemma layered_digraph_compatible_family_common_vertex_paths_common_vertex_same_layer
    {V : Type*} (G : Digraph V) (L : ℕ) (layer : V → ℕ)
    (paths : Set (Fin L → V))
    (h_paths : ∀ P ∈ paths,
      (∀ i : Fin L, layer (P i) = i.val) ∧
      (∀ (i j : Fin L), (j : ℕ) = (i : ℕ) + 1 → G.Adj (P i) (P j)))
    (P Q : Fin L → V) (hP : P ∈ paths) (hQ : Q ∈ paths)
    (v : V) (hi : v ∈ Set.range P) (hj : v ∈ Set.range Q) :
    ∃ k : Fin L, P k = Q k ∧ P k = v := by
  have _ := G
  obtain ⟨i, rfl⟩ := hi
  obtain ⟨j, hj⟩ := hj
  have h1 := (h_paths P hP).1 i
  have h2 := (h_paths Q hQ).1 j
  rw [hj] at h2
  have heq : i = j := by
    ext
    rw [← h1, h2]
  subst heq
  exact ⟨i, hj.symm, rfl⟩

open Classical in
lemma layered_digraph_compatible_family_common_vertex_path_splice_subpath
    {V : Type*} (G : Digraph V) (L : ℕ) (hL : 0 < L) (layer : V → ℕ)
    (paths : Set (Fin L → V))
    (h_paths : ∀ P ∈ paths,
      (∀ i : Fin L, layer (P i) = i.val) ∧
      (∀ (i j : Fin L), (j : ℕ) = (i : ℕ) + 1 → G.Adj (P i) (P j)))
    (h_P1 : ∀ P ∈ paths, ∀ Q : Fin L → V,
      (∀ i : Fin L, layer (Q i) = i.val) →
      (∀ (i j : Fin L), (j : ℕ) = (i : ℕ) + 1 → G.Adj (Q i) (Q j)) →
      Q ⟨0, hL⟩ = P ⟨0, hL⟩ →
      Q ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ = P ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ →
      Q = P)
    (P P0 : Fin L → V) (hP : P ∈ paths) (hP0 : P0 ∈ paths)
    (i j k : Fin L) (hik : i ≤ k) (hkj : k ≤ j)
    (hi : P i = P0 i) (hj : P j = P0 j) :
    P k = P0 k := by
  let R : Fin L → V := fun m => if m < i then P0 m else if m ≤ j then P m else P0 m
  have hR_layer : ∀ m : Fin L, layer (R m) = m.val := by
    intro m
    dsimp [R]
    split_ifs
    · exact (h_paths P0 hP0).1 m
    · exact (h_paths P hP).1 m
    · exact (h_paths P0 hP0).1 m
  have hR_adj : ∀ (m m' : Fin L), (m' : ℕ) = (m : ℕ) + 1 → G.Adj (R m) (R m') := by
    intro m m' hmm'
    have hmm'lt : m < m' := by
      rw [Fin.lt_def, hmm']
      exact Nat.lt_succ_self _
    dsimp [R]
    by_cases hm'i : m' < i
    · have hmi : m < i := lt_trans hmm'lt hm'i
      rw [if_pos hmi, if_pos hm'i]
      exact (h_paths P0 hP0).2 m m' hmm'
    · rw [if_neg hm'i]
      by_cases hm'j : m' ≤ j
      · rw [if_pos hm'j]
        by_cases hmi : m < i
        · rw [if_pos hmi]
          have hm'eq : m' = i := by
            ext
            have : (m : ℕ) < (i : ℕ) := hmi
            have : ¬ (m' : ℕ) < (i : ℕ) := hm'i
            omega
          rw [hm'eq, hi]
          have hmm'2 : (i : ℕ) = (m : ℕ) + 1 := by rw [← hm'eq]; exact hmm'
          exact (h_paths P0 hP0).2 m i hmm'2
        · rw [if_neg hmi]
          have hmj : m ≤ j := le_trans (le_of_lt hmm'lt) hm'j
          rw [if_pos hmj]
          exact (h_paths P hP).2 m m' hmm'
      · rw [if_neg hm'j]
        by_cases hmj : m ≤ j
        · have hmeq : m = j := by
            ext
            have : ¬ (m' : ℕ) ≤ (j : ℕ) := hm'j
            have : (m : ℕ) ≤ (j : ℕ) := hmj
            omega
          have hji : ¬ j < i := not_lt.mpr (le_trans hik hkj)
          rw [hmeq, if_neg hji, if_pos le_rfl, hj]
          have hmm'2 : (m' : ℕ) = (j : ℕ) + 1 := by rw [← hmeq]; exact hmm'
          exact (h_paths P0 hP0).2 j m' hmm'2
        · have hmi : ¬ m < i := by
            intro h
            have : (i : ℕ) ≤ (j : ℕ) := le_trans hik hkj
            have : (m : ℕ) < (i : ℕ) := h
            have : ¬ (m' : ℕ) ≤ (j : ℕ) := hm'j
            omega
          rw [if_neg hmi, if_neg hmj]
          exact (h_paths P0 hP0).2 m m' hmm'
  have hR_zero : R ⟨0, hL⟩ = P0 ⟨0, hL⟩ := by
    dsimp [R]
    split_ifs with h1 h2
    · rfl
    · have h0 : (⟨0, hL⟩ : Fin L) = i := by
        ext
        rw [Fin.lt_def] at h1
        have : (⟨0, hL⟩ : Fin L).val = 0 := rfl
        omega
      rw [h0, hi]
    · rfl
  have hR_last : R ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ = P0 ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ := by
    dsimp [R]
    split_ifs with h1 h2
    · exfalso
      rw [Fin.lt_def] at h1
      have : (i : ℕ) < L := i.is_lt
      have : (⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ : Fin L).val = L - 1 := rfl
      omega
    · have hj_eq : (⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ : Fin L) = j := by
        ext
        have : (j : ℕ) < L := j.is_lt
        have : (⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ : Fin L).val = L - 1 := rfl
        have : (⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ : Fin L).val ≤ (j : ℕ) := h2
        omega
      rw [hj_eq, hj]
    · rfl
  have hR_eq := h_P1 P0 hP0 R hR_layer hR_adj hR_zero hR_last
  have hRk : R k = P k := by
    dsimp [R]
    have : ¬ k < i := not_lt.mpr hik
    rw [if_neg this, if_pos hkj]
  rw [← hRk, hR_eq]

open Classical in
lemma layered_digraph_compatible_family_common_vertex_three_paths_splice
    {V : Type*} (G : Digraph V) (L : ℕ) (hL : 0 < L) (layer : V → ℕ)
    (paths : Set (Fin L → V))
    (h_paths : ∀ P ∈ paths,
      (∀ i : Fin L, layer (P i) = i.val) ∧
      (∀ (i j : Fin L), (j : ℕ) = (i : ℕ) + 1 → G.Adj (P i) (P j)))
    (h_P1 : ∀ P ∈ paths, ∀ Q : Fin L → V,
      (∀ i : Fin L, layer (Q i) = i.val) →
      (∀ (i j : Fin L), (j : ℕ) = (i : ℕ) + 1 → G.Adj (Q i) (Q j)) →
      Q ⟨0, hL⟩ = P ⟨0, hL⟩ →
      Q ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ = P ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ →
      Q = P)
    (P1 P2 P3 : Fin L → V) (hP1 : P1 ∈ paths) (hP2 : P2 ∈ paths) (hP3 : P3 ∈ paths)
    (c1 c2 c3 : Fin L) (hc12 : c1 ≤ c2) (hc23 : c2 ≤ c3)
    (h12 : P1 c1 = P2 c1) (h23 : P2 c2 = P3 c2) (h31 : P3 c3 = P1 c3) :
    P1 c2 = P2 c2 := by
  by_cases h12_eq : c1 = c2
  · subst h12_eq
    exact h12
  by_cases h23_eq : c2 = c3
  · subst h23_eq
    rw [h23, h31]
  have hc12_lt : c1 < c2 := lt_of_le_of_ne hc12 h12_eq
  have hc23_lt : c2 < c3 := lt_of_le_of_ne hc23 h23_eq
  let R : Fin L → V := fun m =>
    if m < c1 then P1 m
    else if m < c2 then P2 m
    else if m ≤ c3 then P3 m
    else P1 m
  have hR_layer : ∀ m : Fin L, layer (R m) = m.val := by
    intro m
    dsimp [R]
    split_ifs
    · exact (h_paths P1 hP1).1 m
    · exact (h_paths P2 hP2).1 m
    · exact (h_paths P3 hP3).1 m
    · exact (h_paths P1 hP1).1 m
  have hR_adj : ∀ (m m' : Fin L), (m' : ℕ) = (m : ℕ) + 1 → G.Adj (R m) (R m') := by
    intro m m' hmm'
    have hmm'lt : m < m' := by
      rw [Fin.lt_def, hmm']
      exact Nat.lt_succ_self _
    dsimp [R]
    by_cases hm'c1 : m' < c1
    · have hmc1 : m < c1 := lt_trans hmm'lt hm'c1
      rw [if_pos hmc1, if_pos hm'c1]
      exact (h_paths P1 hP1).2 m m' hmm'
    · rw [if_neg hm'c1]
      by_cases hm'c2 : m' < c2
      · rw [if_pos hm'c2]
        by_cases hmc1 : m < c1
        · rw [if_pos hmc1]
          have hm'eq : m' = c1 := by
            ext
            have : (m : ℕ) < (c1 : ℕ) := hmc1
            have : ¬ (m' : ℕ) < (c1 : ℕ) := hm'c1
            omega
          rw [hm'eq, ← h12]
          have hmm'2 : (c1 : ℕ) = (m : ℕ) + 1 := by rw [← hm'eq]; exact hmm'
          exact (h_paths P1 hP1).2 m c1 hmm'2
        · rw [if_neg hmc1]
          have hmc2 : m < c2 := lt_trans hmm'lt hm'c2
          rw [if_pos hmc2]
          exact (h_paths P2 hP2).2 m m' hmm'
      · rw [if_neg hm'c2]
        by_cases hm'c3 : m' ≤ c3
        · rw [if_pos hm'c3]
          by_cases hmc2 : m < c2
          · by_cases hmc1 : m < c1
            · exfalso
              have : (c1 : ℕ) ≤ (c2 : ℕ) := hc12
              have : (m : ℕ) < (c1 : ℕ) := hmc1
              have : ¬ (m' : ℕ) < (c2 : ℕ) := hm'c2
              omega
            · rw [if_neg hmc1, if_pos hmc2]
              have hm'eq : m' = c2 := by
                ext
                have : (m : ℕ) < (c2 : ℕ) := hmc2
                have : ¬ (m' : ℕ) < (c2 : ℕ) := hm'c2
                omega
              rw [hm'eq, ← h23]
              have hmm'2 : (c2 : ℕ) = (m : ℕ) + 1 := by rw [← hm'eq]; exact hmm'
              exact (h_paths P2 hP2).2 m c2 hmm'2
          · rw [if_neg (fun h => hmc2 (lt_trans h hc12_lt)), if_neg hmc2]
            have hmc3 : m ≤ c3 := le_trans (le_of_lt hmm'lt) hm'c3
            rw [if_pos hmc3]
            exact (h_paths P3 hP3).2 m m' hmm'
        · rw [if_neg hm'c3]
          by_cases hmc3 : m ≤ c3
          · have hmeq : m = c3 := by
              ext
              have : ¬ (m' : ℕ) ≤ (c3 : ℕ) := hm'c3
              have : (m : ℕ) ≤ (c3 : ℕ) := hmc3
              omega
            have hmc1 : ¬ c3 < c1 := not_lt.mpr (le_trans hc12 hc23)
            have hmc2 : ¬ c3 < c2 := not_lt.mpr hc23
            rw [hmeq, if_neg hmc1, if_neg hmc2, if_pos le_rfl, h31]
            have hmm'2 : (m' : ℕ) = (c3 : ℕ) + 1 := by rw [← hmeq]; exact hmm'
            exact (h_paths P1 hP1).2 c3 m' hmm'2
          · have hmc1 : ¬ m < c1 := by
              intro h
              have : (c1 : ℕ) ≤ (c3 : ℕ) := le_trans hc12 hc23
              have : (m : ℕ) < (c1 : ℕ) := h
              have : ¬ (m' : ℕ) ≤ (c3 : ℕ) := hm'c3
              omega
            have hmc2 : ¬ m < c2 := by
              intro h
              have : (c2 : ℕ) ≤ (c3 : ℕ) := hc23
              have : (m : ℕ) < (c2 : ℕ) := h
              have : ¬ (m' : ℕ) ≤ (c3 : ℕ) := hm'c3
              omega
            rw [if_neg hmc1, if_neg hmc2, if_neg hmc3]
            exact (h_paths P1 hP1).2 m m' hmm'
  have hR_zero : R ⟨0, hL⟩ = P1 ⟨0, hL⟩ := by
    dsimp [R]
    split_ifs with h1 h2 h3
    · rfl
    · have hc1_zero : c1 = ⟨0, hL⟩ := by
        ext
        rw [Fin.lt_def] at h1
        have : (⟨0, hL⟩ : Fin L).val = 0 := rfl
        omega
      rw [hc1_zero] at h12
      rw [← h12]
    · exfalso
      rw [Fin.lt_def] at h2
      have : (c1 : ℕ) < (c2 : ℕ) := hc12_lt
      have : (⟨0, hL⟩ : Fin L).val = 0 := rfl
      omega
    · exfalso
      rw [Fin.lt_def] at h2
      have : (c1 : ℕ) < (c2 : ℕ) := hc12_lt
      have : (⟨0, hL⟩ : Fin L).val = 0 := rfl
      omega
  have hR_last : R ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ = P1 ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ := by
    dsimp [R]
    split_ifs with h1 h2 h3
    · exfalso
      rw [Fin.lt_def] at h1
      have : (c1 : ℕ) < L := c1.is_lt
      have : (⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ : Fin L).val = L - 1 := rfl
      omega
    · exfalso
      rw [Fin.lt_def] at h2
      have : (c2 : ℕ) < L := c2.is_lt
      have : (⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ : Fin L).val = L - 1 := rfl
      omega
    · have hc3_last : c3 = ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ := by
        ext
        have : (c3 : ℕ) < L := c3.is_lt
        have : (⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ : Fin L).val = L - 1 := rfl
        omega
      rw [hc3_last] at h31
      exact h31
    · rfl
  have hR_eq := h_P1 P1 hP1 R hR_layer hR_adj hR_zero hR_last
  have hRc2 : R c2 = P3 c2 := by
    dsimp [R]
    have : ¬ c2 < c1 := not_lt.mpr hc12
    rw [if_neg this, if_neg (lt_irrefl c2), if_pos hc23]
  have : P1 c2 = P3 c2 := by rw [← hRc2, hR_eq]
  rw [this, ← h23]

open Classical in
lemma layered_digraph_compatible_family_common_vertex_three_paths_agree
    {V : Type*} (G : Digraph V) (L : ℕ) (hL : 0 < L) (layer : V → ℕ)
    (paths : Set (Fin L → V))
    (h_paths : ∀ P ∈ paths,
      (∀ i : Fin L, layer (P i) = i.val) ∧
      (∀ (i j : Fin L), (j : ℕ) = (i : ℕ) + 1 → G.Adj (P i) (P j)))
    (h_P1 : ∀ P ∈ paths, ∀ Q : Fin L → V,
      (∀ i : Fin L, layer (Q i) = i.val) →
      (∀ (i j : Fin L), (j : ℕ) = (i : ℕ) + 1 → G.Adj (Q i) (Q j)) →
      Q ⟨0, hL⟩ = P ⟨0, hL⟩ →
      Q ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ = P ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ →
      Q = P)
    (P0 P Q : Fin L → V) (hP0 : P0 ∈ paths) (hP : P ∈ paths) (hQ : Q ∈ paths)
    (k1 k2 k3 : Fin L)
    (h1 : P0 k1 = P k1) (h2 : P k2 = Q k2) (h3 : Q k3 = P0 k3) :
    ∃ k : Fin L, P k = P0 k ∧ Q k = P0 k := by
  have splice := layered_digraph_compatible_family_common_vertex_three_paths_splice G L hL layer paths h_paths h_P1
  rcases le_total k1 k2 with h12 | h21 <;>
  rcases le_total k2 k3 with h23 | h32 <;>
  rcases le_total k1 k3 with h13 | h31
  · -- k1 ≤ k2 ≤ k3
    have := splice P0 P Q hP0 hP hQ k1 k2 k3 h12 h23 h1 h2 h3
    exact ⟨k2, this.symm, by rw [← h2, this.symm]⟩
  · -- k1 ≤ k2, k2 ≤ k3, k3 ≤ k1 => k1 = k2 = k3
    have : k1 = k2 := le_antisymm h12 (le_trans h23 h31)
    subst this
    exact ⟨k1, h1.symm, by rw [← h2, h1.symm]⟩
  · -- k1 ≤ k2, k3 ≤ k2, k1 ≤ k3 => k1 ≤ k3 ≤ k2
    have := splice P P0 Q hP hP0 hQ k1 k3 k2 h13 h32 h1.symm h3.symm h2.symm
    exact ⟨k3, this, h3⟩
  · -- k1 ≤ k2, k3 ≤ k2, k3 ≤ k1 => k3 ≤ k1 ≤ k2
    have := splice Q P0 P hQ hP0 hP k3 k1 k2 h31 h12 h3 h1 h2
    exact ⟨k1, h1.symm, this⟩
  · -- k2 ≤ k1, k2 ≤ k3, k1 ≤ k3 => k2 ≤ k1 ≤ k3
    have := splice Q P P0 hQ hP hP0 k2 k1 k3 h21 h13 h2.symm h1.symm h3.symm
    exact ⟨k1, h1.symm, by rw [this, h1.symm]⟩
  · -- k2 ≤ k1, k2 ≤ k3, k3 ≤ k1 => k2 ≤ k3 ≤ k1
    have := splice P Q P0 hP hQ hP0 k2 k3 k1 h23 h31 h2 h3 h1
    exact ⟨k3, by rw [this, h3], h3⟩
  · -- k2 ≤ k1, k3 ≤ k2, k1 ≤ k3 => k2 = k1 = k3
    have : k2 = k1 := le_antisymm h21 (le_trans h13 h32)
    subst this
    exact ⟨k2, h1.symm, by rw [← h2, h1.symm]⟩
  · -- k2 ≤ k1, k3 ≤ k2, k3 ≤ k1 => k3 ≤ k2 ≤ k1
    have := splice P0 Q P hP0 hQ hP k3 k2 k1 h32 h21 h3.symm h2.symm h1.symm
    exact ⟨k2, by rw [h2, this.symm], this.symm⟩

open Classical in
lemma layered_digraph_compatible_family_common_vertex_path_interval_bounds
    {V : Type*} {L : ℕ} (P P0 : Fin L → V) (h : ∃ k, P k = P0 k) :
    ∃ a b : Fin L, a ≤ b ∧ P a = P0 a ∧ P b = P0 b ∧ (∀ k, P k = P0 k → a ≤ k ∧ k ≤ b) := by
  let s : Finset (Fin L) := Finset.univ.filter (fun k => P k = P0 k)
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
  refine ⟨s.min' hs, s.max' hs, Finset.min'_le_max' s hs, ?_, ?_, ?_⟩
  · have := Finset.min'_mem s hs
    exact (Finset.mem_filter.mp this).2
  · have := Finset.max'_mem s hs
    exact (Finset.mem_filter.mp this).2
  · intro k hk
    have : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
    exact ⟨Finset.min'_le s k this, Finset.le_max' s k this⟩

/-- In a layered DAG, every nonempty compatible family of unique-path critical paths whose compatible pairs overlap shares a common vertex. -/
theorem layered_digraph_compatible_family_common_vertex
    {V : Type*} (G : Digraph V) (L : ℕ) (hL : 0 < L) (layer : V → ℕ)
    (h_dag : is_layered_dag G layer)
    (paths : Set (Fin L → V))
    (h_paths : ∀ P ∈ paths,
      (∀ i : Fin L, layer (P i) = i.val) ∧
      (∀ (i j : Fin L), (j : ℕ) = (i : ℕ) + 1 → G.Adj (P i) (P j)))
    (h_P1 : ∀ P ∈ paths, ∀ Q : Fin L → V,
      (∀ i : Fin L, layer (Q i) = i.val) →
      (∀ (i j : Fin L), (j : ℕ) = (i : ℕ) + 1 → G.Adj (Q i) (Q j)) →
      Q ⟨0, hL⟩ = P ⟨0, hL⟩ →
      Q ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ = P ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩ →
      Q = P)
    (h_P2 : ∀ P ∈ paths, ∀ Q ∈ paths,
      Relation.ReflTransGen G.Adj (P ⟨0, hL⟩) (Q ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩) →
      Relation.ReflTransGen G.Adj (Q ⟨0, hL⟩) (P ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩) →
      ∃ v : V, v ∈ Set.range P ∧ v ∈ Set.range Q)
    (F : Set (Fin L → V)) (hF_nonempty : F.Nonempty) (hF_sub : F ⊆ paths)
    (hF_compat : ∀ P ∈ F, ∀ Q ∈ F,
      Relation.ReflTransGen G.Adj (P ⟨0, hL⟩) (Q ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩)) :
    ∃ v : V, ∀ P ∈ F, v ∈ Set.range P := by
  have _ := h_dag
  obtain ⟨P0, hP0⟩ := hF_nonempty
  have hP0_paths : P0 ∈ paths := hF_sub hP0
  have h_compat_pair : ∀ P ∈ F, ∀ Q ∈ F, ∃ k : Fin L, P k = Q k := by
    intro P hP Q hQ
    have h1 := hF_compat P hP Q hQ
    have h2 := hF_compat Q hQ P hP
    have hP_paths := hF_sub hP
    have hQ_paths := hF_sub hQ
    obtain ⟨v, hvP, hvQ⟩ := h_P2 P hP_paths Q hQ_paths h1 h2
    exact (layered_digraph_compatible_family_common_vertex_paths_common_vertex_same_layer G L layer paths h_paths P Q hP_paths hQ_paths v hvP hvQ).imp (fun k hk => hk.1)
  have h_pair_agree_P0 : ∀ P ∈ F, ∀ Q ∈ F, ∃ k : Fin L, P k = P0 k ∧ Q k = P0 k := by
    intro P hP Q hQ
    obtain ⟨k1, hk1⟩ := h_compat_pair P0 hP0 P hP
    obtain ⟨k2, hk2⟩ := h_compat_pair P hP Q hQ
    obtain ⟨k3, hk3⟩ := h_compat_pair Q hQ P0 hP0
    exact layered_digraph_compatible_family_common_vertex_three_paths_agree G L hL layer paths h_paths h_P1 P0 P Q hP0_paths (hF_sub hP) (hF_sub hQ) k1 k2 k3 hk1 hk2 hk3
  let S : Set (Fin L × Fin L) :=
    { p | ∃ P ∈ F, p.1 ≤ p.2 ∧ P p.1 = P0 p.1 ∧ P p.2 = P0 p.2 ∧ (∀ k, P k = P0 k → p.1 ≤ k ∧ k ≤ p.2) }
  let ι := { p : Fin L × Fin L // p ∈ S }
  have : Finite ι := Subtype.finite
  obtain ⟨k0, hk0⟩ := h_compat_pair P0 hP0 P0 hP0
  obtain ⟨a0, b0, hab0, ha0, hb0, hbound0⟩ := layered_digraph_compatible_family_common_vertex_path_interval_bounds P0 P0 ⟨k0, hk0⟩
  have h0_in_S : (a0, b0) ∈ S := ⟨P0, hP0, hab0, ha0, hb0, hbound0⟩
  have : Nonempty ι := ⟨⟨(a0, b0), h0_in_S⟩⟩
  let a : ι → Fin L := fun i => i.1.1
  let b : ι → Fin L := fun i => i.1.2
  have hab : ∀ i : ι, a i ≤ b i := by
    intro ⟨p, hp⟩
    obtain ⟨P, hP, hle, -⟩ := hp
    exact hle
  have h_inter : ∀ i j : ι, ∃ k : Fin L, a i ≤ k ∧ k ≤ b i ∧ a j ≤ k ∧ k ≤ b j := by
    intro ⟨p, hp⟩ ⟨q, hq⟩
    obtain ⟨P, hP, hPab, hPa, hPb, hPbound⟩ := hp
    obtain ⟨Q, hQ, hQab, hQa, hQb, hQbound⟩ := hq
    obtain ⟨k, hkP, hkQ⟩ := h_pair_agree_P0 P hP Q hQ
    have ⟨haP, hbP⟩ := hPbound k hkP
    have ⟨haQ, hbQ⟩ := hQbound k hkQ
    exact ⟨k, haP, hbP, haQ, hbQ⟩
  obtain ⟨k, hk⟩ := fin_intervals_intersection_nonempty_of_pairwise_inter a b hab h_inter
  have h_all : ∀ P ∈ F, P k = P0 k := by
    intro P hP
    obtain ⟨kP, hkP⟩ := h_compat_pair P hP P0 hP0
    obtain ⟨aP, bP, habP, haP, hbP, hboundP⟩ := layered_digraph_compatible_family_common_vertex_path_interval_bounds P P0 ⟨kP, hkP⟩
    have hP_in_S : (aP, bP) ∈ S := ⟨P, hP, habP, haP, hbP, hboundP⟩
    have hkP_bound := hk ⟨(aP, bP), hP_in_S⟩
    exact layered_digraph_compatible_family_common_vertex_path_splice_subpath G L hL layer paths h_paths h_P1 P P0 (hF_sub hP) hP0_paths aP bP k hkP_bound.1 hkP_bound.2 haP hbP
  refine ⟨P0 k, fun P hP => ⟨k, h_all P hP⟩⟩
