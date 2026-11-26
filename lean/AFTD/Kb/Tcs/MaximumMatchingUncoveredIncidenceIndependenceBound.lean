import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.MaximumMatchingForbidsOneEdgeTwoUncoveredExchange
import AFTD.Kb.Tcs.MaximumMatchingForbidsTwoEdgeThreeEdgeExchange
import AFTD.Kb.Tcs.MaximumMatchingUnmatchedIndependent
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.C

/-!
# maximum_matching_uncovered_incidence_independence_bound

Topic: graphs   Node: 25f00ae1c325

Provenance: helper lemma. Balanced-cut reduction for OP-1957; https://arxiv.org/abs/1011.3384.

For a maximum matching with t uncovered vertices, a global independent-set bound k bounds the number of edges from uncovered vertices to the matched side by t(k−t+1).
-/

private theorem in1214_star_count_of_exchange_rules
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (C U : Finset V) (M : G.Subgraph) [DecidablePred (· ∈ M.verts)] (hM : M.IsMatching)
    (hMC : M.verts ⊆ (C : Set V))
    (hmaxM : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set V) → T.edgeSet.ncard ≤ M.edgeSet.ncard)
    (hU : U = C \ M.verts.toFinset) (t k : ℕ) (ht : 2 ≤ t) (hUcard : U.card = t)
    (hCcard : C.card = 2*k)
    (hind : ∀ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) → I.card ≤ k)
    (hone : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ∀ a b, M.Adj a b → G.Adj u a → ¬ G.Adj v b)
    (htwo : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ∀ a b c d,
      M.Adj a b → M.Adj c d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      G.Adj u a → G.Adj v c → ¬ G.Adj b d) :
    (∑ u ∈ U, ((G.neighborFinset u) ∩ C).card) ≤ t * (k - t + 1) := by
  set_option maxHeartbeats 4000000 in
    classical
    let D : Finset V := M.verts.toFinset
    have hDU : Disjoint D U := by
      apply Finset.disjoint_left.mpr
      intro x hxD hxU
      rw [hU] at hxU
      exact (Finset.mem_sdiff.mp hxU).2 (by simpa [D] using hxD)
    have hDC : D ⊆ C := by intro x hx; exact hMC (by simpa [D] using hx)
    have hUC : U ⊆ C := by rw [hU]; exact Finset.sdiff_subset
    have hUn : ∀ x ∈ U, x ∉ M.verts := by
      intro x hx
      rw [hU] at hx
      simpa [D] using (Finset.mem_sdiff.mp hx).2
    have hUind : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → ¬ G.Adj x y := by
      intro x hx y hy hne
      exact maximum_matching_unmatched_independent G C M hM hMC hmaxM x (hUC hx) (hUn x hx) y (hUC hy) (hUn y hy)
    let f : V → V := fun x => if hx : x ∈ M.verts then Classical.choose (hM hx) else x
    have hf : ∀ x ∈ D, M.Adj x (f x) := by
      intro x hx
      have hxM : x ∈ M.verts := by simpa [D] using hx
      simpa [f,hxM] using (Classical.choose_spec (hM hxM)).1
    have hfD : ∀ x ∈ D, f x ∈ D := by
      intro x hx
      have hh := M.edge_vert (hf x hx).symm
      simpa [D] using hh
    have hfinv : ∀ x ∈ D, f (f x) = x := by
      intro x hx
      have hfxD := hfD x hx
      have h1 := hf (f x) hfxD
      exact (hM (by simpa [D] using hfxD)).unique h1 (hf x hx).symm
    have hfinj : Set.InjOn f (D : Set V) := by
      intro x hx y hy hxy
      have h1 := hfinv x hx
      have h2 := hfinv y hy
      calc
        x = f (f x) := h1.symm
        _ = f (f y) := congrArg f hxy
        _ = y := h2
    let K : V → Finset V := fun x => U.filter (fun u => G.Adj u x)
    let P : Finset V := D.filter (fun x => 2 ≤ (K x).card)
    let Q : Finset V := P.image f
    have hPD : P ⊆ D := Finset.filter_subset _ _
    have hQD : Q ⊆ D := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact hfD y (hPD hy)
    have hQzero : ∀ x ∈ Q, (K x).card = 0 := by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      have haD := hPD ha
      have haK : 2 ≤ (K a).card := (Finset.mem_filter.mp ha).2
      by_contra hn
      obtain ⟨u,hu⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
      have huU : u ∈ U := (Finset.mem_filter.mp hu).1
      have huf : G.Adj u (f a) := (Finset.mem_filter.mp hu).2
      have hnsub : ¬ K a ⊆ {u} := by
        intro hh
        have hc := Finset.card_le_card hh
        simp at hc
        omega
      obtain ⟨v,hv,hvu⟩ := Finset.not_subset.mp hnsub
      have hvU : v ∈ U := (Finset.mem_filter.mp hv).1
      have hva : G.Adj v a := (Finset.mem_filter.mp hv).2
      have hvu' : v ≠ u := by simpa using hvu
      exact hone v hvU u huU hvu' a (f a) (hf a haD) hva huf
    have hPQ : Disjoint P Q := by
      apply Finset.disjoint_left.mpr
      intro x hxP hxQ
      have hp := (Finset.mem_filter.mp hxP).2
      have hq := hQzero x hxQ
      omega
    have hQcard : Q.card = P.card := by
      dsimp [Q]
      apply Finset.card_image_iff.mpr
      exact hfinj.mono (by intro x hx; exact hPD hx)
    have hQU : Disjoint Q U := Finset.disjoint_of_subset_left hQD hDU
    have hQind : ∀ b ∈ Q, ∀ d ∈ Q, b ≠ d → ¬ G.Adj b d := by
      intro b hb d hd hbd hbdEdge
      obtain ⟨a,ha,hfa⟩ := Finset.mem_image.mp hb
      obtain ⟨c,hc,hfc⟩ := Finset.mem_image.mp hd
      have haD := hPD ha
      have hcD := hPD hc
      have hac : a ≠ c := by
        intro he
        apply hbd
        rw [← hfa,← hfc,he]
      have had : a ≠ d := by
        intro he
        have : a ∈ Q := by simpa [he] using hd
        exact Finset.disjoint_left.mp hPQ ha this
      have hbc : b ≠ c := by
        intro he
        have : c ∈ Q := by simpa [he] using hb
        exact Finset.disjoint_left.mp hPQ hc this
      have hKa : 2 ≤ (K a).card := (Finset.mem_filter.mp ha).2
      have hKc : 2 ≤ (K c).card := (Finset.mem_filter.mp hc).2
      obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0 < (K a).card)
      have hnot : ¬ K c ⊆ {u} := by
        intro hh
        have hc' := Finset.card_le_card hh
        simp at hc'
        omega
      obtain ⟨v,hv,hvu⟩ := Finset.not_subset.mp hnot
      have huU : u ∈ U := (Finset.mem_filter.mp hu).1
      have hvU : v ∈ U := (Finset.mem_filter.mp hv).1
      have hvu' : v ≠ u := by simpa using hvu
      have huv : u ≠ v := hvu'.symm
      have hua : G.Adj u a := (Finset.mem_filter.mp hu).2
      have hvc : G.Adj v c := (Finset.mem_filter.mp hv).2
      have hab : M.Adj a b := by simpa [← hfa] using hf a haD
      have hcd : M.Adj c d := by simpa [← hfc] using hf c hcD
      exact htwo u huU v hvU huv a b c d hab hcd hac had hbc hbd hua hvc hbdEdge
    have hUQind : ∀ x ∈ U ∪ Q, ∀ y ∈ U ∪ Q, x ≠ y → ¬ G.Adj x y := by
      intro x hx y hy hne hxy
      rcases Finset.mem_union.mp hx with hxU | hxQ <;> rcases Finset.mem_union.mp hy with hyU | hyQ
      · exact hUind x hxU y hyU hne hxy
      · have hyzero := hQzero y hyQ
        have hmem : x ∈ K y := Finset.mem_filter.mpr ⟨hxU,hxy⟩
        have hp := Finset.card_pos.mpr ⟨x,hmem⟩
        omega
      · have hxzero := hQzero x hxQ
        have hmem : y ∈ K x := Finset.mem_filter.mpr ⟨hyU,hxy.symm⟩
        have hp := Finset.card_pos.mpr ⟨y,hmem⟩
        omega
      · exact hQind x hxQ y hyQ hne hxy
    have hpbound : P.card + t ≤ k := by
      have hh := hind (U ∪ Q) hUQind
      have hc := Finset.card_union_of_disjoint hQU.symm
      rw [hUcard,hQcard] at hc
      omega
    have hDcard : D.card = 2*M.edgeSet.ncard := by
      dsimp [D]
      rw [← Set.ncard_eq_toFinset_card']
      exact (in1076_matching_twice_card hM).symm
    have htcard : D.card+t=2*k := by
      have hh := Finset.card_sdiff_add_card_eq_card hDC
      rw [← hU,hUcard,hCcard] at hh
      omega
    have hUCcount : ∀ u ∈ U, ((G.neighborFinset u) ∩ C).card = ((G.neighborFinset u) ∩ D).card := by
      intro u hu
      congr 1
      ext x
      constructor
      · intro hx
        have hxN := (Finset.mem_inter.mp hx).1
        have hxC := (Finset.mem_inter.mp hx).2
        by_cases hxD : x ∈ D
        · exact Finset.mem_inter.mpr ⟨hxN,hxD⟩
        · have hxU : x ∈ U := by rw [hU]; exact Finset.mem_sdiff.mpr ⟨hxC,hxD⟩
          have hux : G.Adj u x := by simpa using hxN
          exact False.elim (hUind u hu x hxU (G.ne_of_adj hux) hux)
      · intro hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,hDC (Finset.mem_inter.mp hx).2⟩
    have hsumEq : (∑ u ∈ U, ((G.neighborFinset u) ∩ C).card) = ∑ x ∈ D, (K x).card := by
      have hAbove : ∀ u, D.filter (fun x => G.Adj u x) = (G.neighborFinset u) ∩ D := by
        intro u; ext x; simp [and_comm]
      have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=U) (t:=D) G.Adj
      simp only [Finset.bipartiteAbove,Finset.bipartiteBelow,hAbove] at hh
      calc
        (∑ u ∈ U, ((G.neighborFinset u) ∩ C).card) =
            (∑ u ∈ U, ((G.neighborFinset u) ∩ D).card) := by
              apply Finset.sum_congr rfl
              intro u hu
              exact hUCcount u hu
        _ = ∑ x ∈ D, (K x).card := by simpa [K] using hh
    let L : Finset V := D \ (P ∪ Q)
    have hL : ∀ x ∈ L, (K x).card ≤ 1 := by
      intro x hx
      have hxD := (Finset.mem_sdiff.mp hx).1
      have hnP : x ∉ P := by intro hp; exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left Q hp)
      by_contra hn
      apply hnP
      exact Finset.mem_filter.mpr ⟨hxD,by omega⟩
    have hcover : P ∪ Q ∪ L = D := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · rcases Finset.mem_union.mp hx with hx | hx
          · exact hPD hx
          · exact hQD hx
        · exact (Finset.mem_sdiff.mp hx).1
      · intro hx
        by_cases hp : x ∈ P
        · exact Finset.mem_union_left L (Finset.mem_union_left Q hp)
        · by_cases hq : x ∈ Q
          · exact Finset.mem_union_left L (Finset.mem_union_right P hq)
          · exact Finset.mem_union_right (P ∪ Q) (Finset.mem_sdiff.mpr ⟨hx,by simp [hp,hq]⟩)
    have hPL : Disjoint P L := by
      apply Finset.disjoint_left.mpr
      intro x hxP hxL
      exact (Finset.mem_sdiff.mp hxL).2 (Finset.mem_union_left Q hxP)
    have hQL : Disjoint Q L := by
      apply Finset.disjoint_left.mpr
      intro x hxQ hxL
      exact (Finset.mem_sdiff.mp hxL).2 (Finset.mem_union_right P hxQ)
    have hPQL : Disjoint (P ∪ Q) L := Finset.disjoint_union_left.mpr ⟨hPL,hQL⟩
    have hsumBound : (∑ x ∈ D, (K x).card) ≤ t*P.card+L.card := by
      rw [← hcover,Finset.sum_union hPQL,Finset.sum_union hPQ]
      have hsumP : (∑ x ∈ P, (K x).card) ≤ t*P.card := by
        have hh := Finset.sum_le_sum (s:=P) (fun x _ => Finset.card_filter_le U (fun u => G.Adj u x))
        simpa [K,hUcard,Nat.mul_comm] using hh
      have hsumQ : (∑ x ∈ Q, (K x).card) = 0 := by
        exact Finset.sum_eq_zero hQzero
      have hsumL : (∑ x ∈ L, (K x).card) ≤ L.card := by
        have hh := Finset.sum_le_sum (s:=L) hL
        simpa using hh
      omega
    have hcardD : P.card+Q.card+L.card=D.card := by
      have hh := Finset.card_union_of_disjoint hPQL
      have hg := Finset.card_union_of_disjoint hPQ
      rw [hcover] at hh
      omega
    have htk : t ≤ k := by omega
    have hrew : k-t+t=k := by omega
    have htwot : t-2+2=t := by omega
    have hprod := Nat.mul_le_mul_left (t-2) (by omega : P.card ≤ k-t)
    have hpP := congrArg (fun n : ℕ => n*P.card) htwot
    have hpK := congrArg (fun n : ℕ => n*(k-t)) htwot
    have hkt := congrArg (fun n : ℕ => t*n) hrew
    simp only [Nat.add_mul,Nat.mul_add] at hpP hpK hkt
    rw [hsumEq]
    nlinarith

theorem maximum_matching_uncovered_incidence_independence_bound
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (C U : Finset V) (M : G.Subgraph) [DecidablePred (· ∈ M.verts)] (hM : M.IsMatching)
    (hMC : M.verts ⊆ (C : Set V))
    (hmaxM : ∀ T : G.Subgraph, T.IsMatching → T.verts ⊆ (C : Set V) → T.edgeSet.ncard ≤ M.edgeSet.ncard)
    (hU : U = C \ M.verts.toFinset) (t k : ℕ) (ht : 2 ≤ t) (hUcard : U.card = t)
    (hCcard : C.card = 2*k)
    (hind : ∀ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) → I.card ≤ k) :
    (∑ u ∈ U, ((G.neighborFinset u) ∩ C).card) ≤ t * (k - t + 1) := by
  set_option maxHeartbeats 4000000 in
    classical
    have hUC : U ⊆ C := by rw [hU]; exact Finset.sdiff_subset
    have hUn : ∀ u ∈ U, u ∉ M.verts := by
      intro u hu
      rw [hU] at hu
      simpa using (Finset.mem_sdiff.mp hu).2
    apply in1214_star_count_of_exchange_rules G C U M hM hMC hmaxM hU t k ht hUcard hCcard hind
    · intro u hu v hv huv a b hab hua hvb
      exact maximum_matching_forbids_one_edge_two_uncovered_exchange G C M hM hMC hmaxM
        u v a b (hUC hu) (hUC hv) (hUn u hu) (hUn v hv) huv hab hua hvb
    · intro u hu v hv huv a b c d hab hcd hac had hbc hbd hua hvc hbdEdge
      exact maximum_matching_forbids_two_edge_three_edge_exchange G C M hM hMC hmaxM
        u v a b c d (hUC hu) (hUC hv) (hUn u hu) (hUn v hv) huv hab hcd hac had hbc hbd hua hvc hbdEdge
