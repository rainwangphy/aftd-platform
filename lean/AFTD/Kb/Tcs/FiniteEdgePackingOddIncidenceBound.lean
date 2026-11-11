import AFTD.Prelude

/-!
# finite_edge_packing_odd_incidence_bound

Topic: graphs   Node: 5457d57a0dbe

Provenance: helper lemma. Odd-degree packing bound for ten_vertex_exchange_packing_upper.

For a finite set of undirected edges E and a pairwise edge-disjoint family P of three-edge sets, if each member of P has even incidence at every vertex and every vertex in O has odd incidence in E, then 3|P| + ceil(|O|/2) ≤ |E|.
-/

theorem finite_edge_packing_odd_incidence_bound {V : Type} [DecidableEq V]
    (E : Finset (Sym2 V)) (P : Finset (Finset (Sym2 V))) (O : Finset V)
    (hsub : ∀ t ∈ P, t ⊆ E)
    (hdisj : (P : Set (Finset (Sym2 V))).Pairwise Disjoint)
    (hsize : ∀ t ∈ P, t.card = 3)
    (heven : ∀ v : V, ∀ t ∈ P, Even ((t.filter (fun e => v ∈ e)).card))
    (hodd : ∀ v ∈ O, Odd ((E.filter (fun e => v ∈ e)).card)) :
    3 * P.card + (O.card + 1) / 2 ≤ E.card := by
  classical
  let U : Finset (Sym2 V) := P.biUnion id
  let D : Finset (Sym2 V) := E \ U
  have hUE : U ⊆ E := by
    intro e he
    obtain ⟨t,ht,het⟩ := Finset.mem_biUnion.mp he
    exact hsub t ht het
  have hpair : (P : Set (Finset (Sym2 V))).PairwiseDisjoint (fun t => t) := hdisj
  have hUcard : U.card = 3 * P.card := by
    change (P.biUnion fun t => t).card = 3 * P.card
    rw [Finset.card_biUnion hpair]
    calc
      _ = ∑ _t ∈ P, 3 := Finset.sum_congr rfl (fun t ht => hsize t ht)
      _ = 3 * P.card := by simp [Nat.mul_comm]
  have hEvenU (v : V) : Even ((U.filter (fun e => v ∈ e)).card) := by
    dsimp only [U]
    change Even (((P.biUnion fun t => t).filter (fun e => v ∈ e)).card)
    rw [Finset.filter_biUnion, Finset.card_biUnion (Finset.pairwiseDisjoint_filter hpair (fun e => v ∈ e))]
    exact Finset.even_sum _ (fun t ht => heven v t ht)
  have hCover : O ⊆ D.biUnion (fun e => e.toFinset) := by
    intro v hv
    by_contra hn
    have hno : ∀ e ∈ D, v ∉ e := by
      intro e he hve
      apply hn
      exact Finset.mem_biUnion.mpr ⟨e,he,Sym2.mem_toFinset.mpr hve⟩
    have hEq : E.filter (fun e => v ∈ e) = U.filter (fun e => v ∈ e) := by
      apply Finset.Subset.antisymm
      · intro e he
        obtain ⟨heE,hve⟩ := Finset.mem_filter.mp he
        have heU : e ∈ U := by
          by_contra hnot
          exact hno e (Finset.mem_sdiff.mpr ⟨heE,hnot⟩) hve
        exact Finset.mem_filter.mpr ⟨heU,hve⟩
      · intro e he
        obtain ⟨heU,hve⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨hUE heU,hve⟩
    have hne : ¬Even ((E.filter (fun e => v ∈ e)).card) := Nat.not_even_iff_odd.mpr (hodd v hv)
    apply hne
    rw [hEq]
    exact hEvenU v
  have hcard : O.card ≤ 2 * D.card := by
    calc
      O.card ≤ (D.biUnion (fun e => e.toFinset)).card := Finset.card_le_card hCover
      _ ≤ ∑ e ∈ D, (e.toFinset).card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ D, 2 := by
        apply Finset.sum_le_sum
        intro e he
        rw [Sym2.card_toFinset]
        split_ifs <;> omega
      _ = 2 * D.card := by simp [Nat.mul_comm]
  have hDcard : D.card = E.card - U.card := Finset.card_sdiff_of_subset hUE
  have hle : U.card ≤ E.card := Finset.card_le_card hUE
  omega
