import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfIsColorConnecting
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# wild_number_complete_graph_two_coloring_range

Topic: graphs   Node: 3f87b8f117e5

Provenance: formalization of a published result. Source: arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Theorem 3.1 (with 0 ≤ wld automatic in ℕ).

Let n ≥ 4. Every (surjective) 2-edge-colouring of K_n has wild number at most n − 2, and every integer 0 ≤ k ≤ n − 2 is the wild number of some 2-edge-colouring of K_n.
-/

theorem wild_two_reachable_of_adj_reachable {V : Type*} {G G' : SimpleGraph V}
    (h : ∀ x y, G.Adj x y → G'.Reachable x y) {u v : V} (huv : G.Reachable u v) :
    G'.Reachable u v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

theorem wild_two_card_le_of_connected {V : Type*} [Fintype V] (S : Set (Sym2 V))
    (R : Finset (Sym2 V)) (hS : (SimpleGraph.fromEdgeSet S).Connected) (hR : S ⊆ ↑R) :
    Fintype.card V ≤ R.card + 1 := by
  have hc := hS.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at hc
  have : Nat.card (SimpleGraph.fromEdgeSet S).edgeSet ≤ R.card := by
    rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    apply Nat.card_mono (Finset.finite_toSet R)
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact Set.sdiff_subset.trans hR
  omega

theorem wild_two_wild_number_eq_of {V α : Type*} (G : SimpleGraph V) (γ : G.edgeSet → α) (k : ℕ)
    (W0 : Finset (Sym2 V)) (hW0 : simple_graph_is_color_connecting G γ ↑W0) (hk : W0.card ≤ k)
    (hlow : ∀ W : Finset (Sym2 V), simple_graph_is_color_connecting G γ ↑W → k ≤ W.card) :
    simple_graph_wild_number G γ = k := by
  apply le_antisymm
  · exact (simple_graph_wild_number_le_of_is_color_connecting G γ W0 hW0).trans hk
  · exact le_csInf ⟨_, W0, rfl, hW0⟩ fun j ⟨W, hj, hW⟩ => by rw [← hj]; exact hlow W hW

theorem wild_two_top_mem_edgeSet {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    s(i, j) ∈ (⊤ : SimpleGraph (Fin n)).edgeSet := by
  simpa using h

/-- Upper bound: some colour class is connected; join the components of the other one by a star. -/
theorem wild_two_upper (n : ℕ) (hn : 4 ≤ n) (γ : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin 2)
    (hγ : Function.Surjective γ) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) γ ≤ n - 2 := by
  classical
  let H : Fin 2 → SimpleGraph (Fin n) := fun c =>
    SimpleGraph.fromEdgeSet {f | ∃ hf : f ∈ (⊤ : SimpleGraph (Fin n)).edgeSet, γ ⟨f, hf⟩ = c}
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hHadj : ∀ c x y (hxy : x ≠ y),
      (H c).Adj x y ↔ γ ⟨s(x, y), wild_two_top_mem_edgeSet hxy⟩ = c := by
    intro c x y hxy
    simp only [H, SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hf, hc⟩, -⟩; exact hc
    · intro hc; exact ⟨⟨wild_two_top_mem_edgeSet hxy, hc⟩, hxy⟩
  have hcompl : ∀ c x y, x ≠ y → ¬ (H c).Adj x y → (H (1 - c)).Adj x y := by
    intro c x y hxy h
    rw [hHadj c x y hxy] at h
    rw [hHadj (1 - c) x y hxy]
    revert h
    generalize γ ⟨s(x, y), wild_two_top_mem_edgeSet hxy⟩ = a
    fin_cases a <;> fin_cases c <;> simp
  -- one of the two classes is connected
  have hone : ∃ c, (H c).Connected := by
    by_cases h0 : (H 0).Connected
    · exact ⟨0, h0⟩
    · refine ⟨1, ?_⟩
      have h0' : ¬ (H 0).Preconnected := fun hp => h0 ⟨hp⟩
      simp only [SimpleGraph.Preconnected, not_forall] at h0'
      obtain ⟨a, b, hab⟩ := h0'
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨a, fun y => ?_⟩
      by_cases hy : (H 0).Reachable a y
      · -- y is in a's component: go through b
        have hby : ¬ (H 0).Reachable b y := fun h => hab (hy.trans h.symm)
        have hab' : a ≠ b := fun h => hab (h ▸ SimpleGraph.Reachable.refl _)
        have hby' : b ≠ y := fun h => hby (h ▸ SimpleGraph.Reachable.refl _)
        have h1 : (H 1).Adj a b := hcompl 0 a b hab' (fun h => hab h.reachable)
        have h2 : (H 1).Adj b y := hcompl 0 b y hby' (fun h => hby h.reachable)
        exact h1.reachable.trans h2.reachable
      · have hay : a ≠ y := fun h => hy (h ▸ SimpleGraph.Reachable.refl _)
        exact (hcompl 0 a y hay (fun h => hy h.reachable)).reachable
  obtain ⟨c1, hc1⟩ := hone
  set c0 := 1 - c1 with hc0
  have hγc : ∀ e, γ e = c0 ∨ γ e = c1 := by
    intro e
    generalize γ e = a
    fin_cases a <;> fin_cases c1 <;> simp [hc0]
  -- representatives of the components of H c0
  let r : (H c0).ConnectedComponent → Fin n := fun C => Quot.out C
  have hr : ∀ C, (H c0).connectedComponentMk (r C) = C := fun C => Quot.out_eq C
  let C0 := (H c0).connectedComponentMk ⟨0, by omega⟩
  let W : Finset (Sym2 (Fin n)) := (Finset.univ.erase C0).image fun C => s(r C0, r C)
  have hrne : ∀ C, C ≠ C0 → r C0 ≠ r C := by
    intro C hC h
    apply hC
    rw [← hr C, ← hr C0, h]
  have hW : simple_graph_is_color_connecting (⊤ : SimpleGraph (Fin n)) γ ↑W := by
    refine ⟨?_, fun e => ?_⟩
    · intro f hf
      simp only [W, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_erase] at hf
      obtain ⟨C, ⟨hC, -⟩, rfl⟩ := hf
      exact wild_two_top_mem_edgeSet (hrne C hC)
    · rcases hγc e with he | he
      · rw [he]
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        refine ⟨r C0, fun y => ?_⟩
        have hle : H c0 ≤ SimpleGraph.fromEdgeSet
            ({f | ∃ hf : f ∈ (⊤ : SimpleGraph (Fin n)).edgeSet, γ ⟨f, hf⟩ = c0} ∪ ↑W) :=
          SimpleGraph.fromEdgeSet_mono Set.subset_union_left
        have hy : (H c0).Reachable (r ((H c0).connectedComponentMk y)) y :=
          SimpleGraph.ConnectedComponent.exact (hr _)
        by_cases hC : (H c0).connectedComponentMk y = C0
        · rw [hC] at hy
          exact hy.mono hle
        · refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) (hy.mono hle)
          rw [SimpleGraph.fromEdgeSet_adj]
          refine ⟨Or.inr ?_, hrne _ hC⟩
          simp only [W, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_erase,
            Finset.mem_univ, and_true]
          exact ⟨_, hC, rfl⟩
      · rw [he]
        exact hc1.mono (SimpleGraph.fromEdgeSet_mono Set.subset_union_left)
  refine (simple_graph_wild_number_le_of_is_color_connecting _ γ W hW).trans ?_
  -- H c0 has an edge, so it has fewer than n components
  obtain ⟨⟨f, hf⟩, he⟩ := hγ c0
  induction f using Sym2.ind with
  | h x y =>
  have hxy' : x ≠ y := by simpa using hf
  have hadj : (H c0).Adj x y := (hHadj c0 x y hxy').2 he
  have hcard : Fintype.card (H c0).ConnectedComponent < n := by
    have := Fintype.card_lt_of_surjective_not_injective (H c0).connectedComponentMk
      (fun C => ⟨r C, hr C⟩) (fun hinj => hxy' (hinj (SimpleGraph.ConnectedComponent.sound hadj.reachable)))
    simpa using this
  have hWc : W.card ≤ (Finset.univ.erase C0).card := Finset.card_image_le
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hWc
  omega

def wild_two_path_color (n : ℕ) : Sym2 (Fin n) → Fin 2 :=
  Sym2.lift ⟨fun i j => if i.val + 1 = j.val ∨ j.val + 1 = i.val then 0 else 1,
    fun i j => by simp only [or_comm]⟩

def wild_two_block_color (n k : ℕ) : Sym2 (Fin n) → Fin 2 :=
  Sym2.lift ⟨fun i j => if i.val < n - k ∧ j.val < n - k then 0 else 1,
    fun i j => by simp only [and_comm]⟩

theorem wild_two_fromEdgeSet_adj {n : ℕ} (γ : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin 2) (c : Fin 2)
    (W : Set (Sym2 (Fin n))) (x y : Fin n) :
    (SimpleGraph.fromEdgeSet ({f | ∃ hf : f ∈ (⊤ : SimpleGraph (Fin n)).edgeSet, γ ⟨f, hf⟩ = c} ∪ W)).Adj x y ↔
      ∃ hxy : x ≠ y, (γ ⟨s(x, y), wild_two_top_mem_edgeSet hxy⟩ = c ∨ s(x, y) ∈ W) := by
  simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h | h, hxy⟩
    · exact ⟨hxy, Or.inl h.2⟩
    · exact ⟨hxy, Or.inr h⟩
  · rintro ⟨hxy, h | h⟩
    · exact ⟨Or.inl ⟨wild_two_top_mem_edgeSet hxy, h⟩, hxy⟩
    · exact ⟨Or.inr h, hxy⟩

theorem wild_two_fromEdgeSet_adj' {n : ℕ} (γ : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin 2) (c : Fin 2)
    (x y : Fin n) :
    (SimpleGraph.fromEdgeSet {f | ∃ hf : f ∈ (⊤ : SimpleGraph (Fin n)).edgeSet, γ ⟨f, hf⟩ = c}).Adj x y ↔
      ∃ hxy : x ≠ y, γ ⟨s(x, y), wild_two_top_mem_edgeSet hxy⟩ = c := by
  have := wild_two_fromEdgeSet_adj γ c ∅ x y
  simpa using this

theorem wild_two_attain (n : ℕ) (hn : 4 ≤ n) (k : ℕ) (hk : k ≤ n - 2) :
    ∃ γ : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin 2, Function.Surjective γ ∧
      simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) γ = k := by
  classical
  have h0n : 0 < n := by omega
  haveI : Nonempty (Fin n) := ⟨⟨0, h0n⟩⟩
  have two : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- k = 0: a Hamiltonian path and its complement
    let γ : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin 2 := fun e => wild_two_path_color n e.1
    refine ⟨γ, ?_, ?_⟩
    · intro c
      rcases two c with rfl | rfl
      · exact ⟨⟨s(⟨0, h0n⟩, ⟨1, by omega⟩), wild_two_top_mem_edgeSet (by simp [Fin.ext_iff])⟩,
          by simp [γ, wild_two_path_color]⟩
      · exact ⟨⟨s(⟨0, h0n⟩, ⟨2, by omega⟩), wild_two_top_mem_edgeSet (by simp [Fin.ext_iff])⟩,
          by simp [γ, wild_two_path_color]⟩
    · refine wild_two_wild_number_eq_of _ _ 0 ∅ ⟨by simp, fun e => ?_⟩ (by simp) (fun _ _ => by simp)
      rw [Finset.coe_empty, Set.union_empty, SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨0, h0n⟩, fun y => ?_⟩
      rcases two (γ e) with hce | hce
      · -- the path
        obtain ⟨m, hm⟩ := y
        induction m with
        | zero => exact SimpleGraph.Reachable.refl _
        | succ m ih =>
          refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
          rw [wild_two_fromEdgeSet_adj' γ]
          exact ⟨by simp [Fin.ext_iff], by rw [hce]; simp [γ, wild_two_path_color]⟩
      · -- the complement of the path (n ≥ 4)
        obtain ⟨m, hm⟩ := y
        rcases Nat.lt_or_ge m 2 with h2 | h2
        · interval_cases m
          · exact SimpleGraph.Reachable.refl _
          · have a1 : (SimpleGraph.fromEdgeSet {f | ∃ hf : f ∈ (⊤ : SimpleGraph (Fin n)).edgeSet,
                γ ⟨f, hf⟩ = γ e}).Adj ⟨0, h0n⟩ ⟨3, by omega⟩ := by
              rw [wild_two_fromEdgeSet_adj' γ]
              exact ⟨by simp [Fin.ext_iff], by rw [hce]; simp [γ, wild_two_path_color]⟩
            have a2 : (SimpleGraph.fromEdgeSet {f | ∃ hf : f ∈ (⊤ : SimpleGraph (Fin n)).edgeSet,
                γ ⟨f, hf⟩ = γ e}).Adj ⟨3, by omega⟩ ⟨1, hm⟩ := by
              rw [wild_two_fromEdgeSet_adj' γ]
              exact ⟨by simp [Fin.ext_iff], by rw [hce]; simp [γ, wild_two_path_color]⟩
            exact a1.reachable.trans a2.reachable
        · apply SimpleGraph.Adj.reachable
          rw [wild_two_fromEdgeSet_adj' γ]
          refine ⟨by simp [Fin.ext_iff]; omega, ?_⟩
          rw [hce]
          simp [γ, wild_two_path_color] <;> omega
  · -- k ≥ 1: a clique on n - k vertices, all other pairs coloured 1
    let γ : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin 2 := fun e => wild_two_block_color n k e.1
    have hcol : ∀ x y : Fin n, wild_two_block_color n k s(x, y) =
        if x.val < n - k ∧ y.val < n - k then 0 else 1 := fun x y => rfl
    let z : Fin n := ⟨0, h0n⟩
    let last : Fin n := ⟨n - 1, by omega⟩
    refine ⟨γ, ?_, ?_⟩
    · intro c
      rcases two c with rfl | rfl
      · refine ⟨⟨s(z, ⟨1, by omega⟩), wild_two_top_mem_edgeSet (by simp [z, Fin.ext_iff])⟩, ?_⟩
        show wild_two_block_color n k s(z, ⟨1, by omega⟩) = 0
        rw [hcol, if_pos (by simp [z]; omega)]
      · refine ⟨⟨s(z, last), wild_two_top_mem_edgeSet (by simp [z, last, Fin.ext_iff]; omega)⟩, ?_⟩
        show wild_two_block_color n k s(z, last) = 1
        rw [hcol, if_neg (by simp [z, last]; omega)]
    · let W0 : Finset (Sym2 (Fin n)) :=
        (Finset.range k).image fun t => s(z, (⟨n - 1 - t, by omega⟩ : Fin n))
      have hW0mem : ∀ j : Fin n, n - k ≤ j.val → s(z, j) ∈ W0 := fun j hj => by
        simp only [W0, Finset.mem_image, Finset.mem_range]
        refine ⟨n - 1 - j.val, by omega, ?_⟩
        congr 1
        exact Fin.ext (by simp; omega)
      have hW0card : W0.card ≤ k := Finset.card_image_le.trans (by simp)
      have hW0 : simple_graph_is_color_connecting (⊤ : SimpleGraph (Fin n)) γ ↑W0 := by
        refine ⟨?_, fun e => ?_⟩
        · intro f hf
          simp only [W0, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hf
          obtain ⟨t, ht, rfl⟩ := hf
          exact wild_two_top_mem_edgeSet (by simp only [ne_eq, Fin.ext_iff, z]; omega)
        · rw [SimpleGraph.connected_iff_exists_forall_reachable]
          rcases two (γ e) with hce | hce
          · refine ⟨z, fun y => ?_⟩
            by_cases hyz : y = z
            · rw [hyz]
            apply SimpleGraph.Adj.reachable
            rw [wild_two_fromEdgeSet_adj γ]
            refine ⟨Ne.symm hyz, ?_⟩
            by_cases hy : y.val < n - k
            · left
              rw [hce]
              show wild_two_block_color n k s(z, y) = 0
              rw [hcol, if_pos ⟨by simp [z]; omega, hy⟩]
            · right
              exact Finset.mem_coe.2 (hW0mem y (by omega))
          · refine ⟨last, fun y => ?_⟩
            by_cases hyl : y = last
            · rw [hyl]
            apply SimpleGraph.Adj.reachable
            rw [wild_two_fromEdgeSet_adj γ]
            refine ⟨Ne.symm hyl, Or.inl ?_⟩
            rw [hce]
            show wild_two_block_color n k s(last, y) = 1
            rw [hcol, if_neg (by simp [last]; omega)]
      refine wild_two_wild_number_eq_of _ _ k W0 hW0 hW0card (fun W hW => ?_)
      -- lower bound: transfer connectivity of (class 0) ∪ W to (a star in the clique) ∪ W
      let P : Finset (Sym2 (Fin n)) :=
        (Finset.range (n - k - 1)).image fun t => s(z, (⟨(t + 1) % n, Nat.mod_lt _ h0n⟩ : Fin n))
      have hPcard : P.card ≤ n - k - 1 := Finset.card_image_le.trans (by simp)
      have he01 : s(z, (⟨1, by omega⟩ : Fin n)) ∈ (⊤ : SimpleGraph (Fin n)).edgeSet :=
        wild_two_top_mem_edgeSet (by simp [Fin.ext_iff, z])
      have hconn := hW.2 ⟨_, he01⟩
      have hc0 : γ ⟨_, he01⟩ = 0 := by
        show wild_two_block_color n k s(z, ⟨1, by omega⟩) = 0
        rw [hcol, if_pos (by simp [z]; omega)]
      rw [hc0] at hconn
      have hstar : ∀ x : Fin n, x.val < n - k →
          (SimpleGraph.fromEdgeSet (↑P ∪ ↑W : Set (Sym2 (Fin n)))).Reachable z x := by
        intro x hx
        by_cases hxz : x = z
        · rw [hxz]
        apply SimpleGraph.Adj.reachable
        rw [SimpleGraph.fromEdgeSet_adj]
        refine ⟨Or.inl ?_, Ne.symm hxz⟩
        simp only [P, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
        have : x.val ≠ 0 := fun h => hxz (Fin.ext h)
        refine ⟨x.val - 1, by omega, ?_⟩
        congr 1
        exact Fin.ext (by simp only; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      have hconn' : (SimpleGraph.fromEdgeSet (↑P ∪ ↑W : Set (Sym2 (Fin n)))).Connected := by
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        refine ⟨z, fun y => wild_two_reachable_of_adj_reachable ?_ (hconn.preconnected z y)⟩
        intro a b hab
        rw [wild_two_fromEdgeSet_adj γ] at hab
        obtain ⟨hab, h | h⟩ := hab
        · have h' : wild_two_block_color n k s(a, b) = 0 := h
          rw [hcol] at h'
          split_ifs at h' with hh
          · exact (hstar a hh.1).symm.trans (hstar b hh.2)
          · exact absurd h' (by decide)
        · apply SimpleGraph.Adj.reachable
          rw [SimpleGraph.fromEdgeSet_adj]
          exact ⟨Or.inr h, hab⟩
      have h1 := wild_two_card_le_of_connected _ (P ∪ W) hconn' (by rw [Finset.coe_union])
      rw [Fintype.card_fin] at h1
      have h2 := Finset.card_union_le P W
      omega

theorem wild_number_complete_graph_two_coloring_range (n : ℕ) (hn : 4 ≤ n) :
    (∀ γ : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin 2, Function.Surjective γ →
        simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) γ ≤ n - 2) ∧
      ∀ k ≤ n - 2, ∃ γ : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin 2, Function.Surjective γ ∧
        simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) γ = k := by
  exact ⟨fun γ hγ => wild_two_upper n hn γ hγ, fun k hk => wild_two_attain n hn k hk⟩
