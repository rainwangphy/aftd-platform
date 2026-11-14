import AFTD.Prelude
import AFTD.Kb.Tcs.IsTotalEdgeIrregularLabeling
import AFTD.Kb.Tcs.SimpleGraphEndpointSumEdges

/-!
# admissibility_lemma_sufficiency

Topic: graphs   Node: d5c849603047

Provenance: helper lemma. arXiv:2611.16338, Lemma 2.1

Let s ≥ 3, let G be a finite simple graph, and let φ : V → ℕ be a vertex labeling such that φ(v) ∈ {1, s} for all v. Let a = |E_2|, b = |E_{s+1}|, and c = |E_{2s}| be the counts of edges with endpoint label sums 2, s + 1, and 2s, respectively. If a ≤ s, b ≤ s, c ≤ s, a + b ≤ 2s - 1, b + c ≤ 2s - 1, and a + b + c ≤ 3s - 2, then φ extends to a total edge irregular s-labeling of G.
-/

theorem admissibility_lemma_sufficiency_equivFin_val_inj {α : Type*}
    (S : Finset α) (x y : α) (hx : x ∈ S) (hy : y ∈ S)
    (h : (S.equivFin ⟨x, hx⟩).val = (S.equivFin ⟨y, hy⟩).val) : x = y := by
  have h1 : S.equivFin ⟨x, hx⟩ = S.equivFin ⟨y, hy⟩ := Fin.ext h
  have h2 : (⟨x, hx⟩ : S) = ⟨y, hy⟩ := S.equivFin.injective h1
  exact Subtype.ext_iff.mp h2

open scoped Classical in
/-- Sufficiency direction of the admissibility lemma for binary vertex labelings. -/
theorem admissibility_lemma_sufficiency {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : ℕ) (hs : 3 ≤ s) (φ : V → ℕ)
    (hφ : ∀ v : V, φ v = 1 ∨ φ v = s)
    (h_ineq : let a := (simple_graph_endpoint_sum_edges G φ 2).card
              let b := (simple_graph_endpoint_sum_edges G φ (s + 1)).card
              let c := (simple_graph_endpoint_sum_edges G φ (2 * s)).card
              a ≤ s ∧ b ≤ s ∧ c ≤ s ∧ a + b ≤ 2 * s - 1 ∧ b + c ≤ 2 * s - 1 ∧ a + b + c ≤ 3 * s - 2) :
    ∃ ψ : G.edgeSet → ℕ, is_total_edge_irregular_labeling G s φ ψ := by
  let E2 := simple_graph_endpoint_sum_edges G φ 2
  let Eb := simple_graph_endpoint_sum_edges G φ (s + 1)
  let Ec := simple_graph_endpoint_sum_edges G φ (2 * s)
  let a := E2.card
  let b := Eb.card
  let c := Ec.card
  rcases h_ineq with ⟨ha, hb, hc, hab, hbc, habc⟩
  change E2.card ≤ s at ha
  change Eb.card ≤ s at hb
  change Ec.card ≤ s at hc
  change E2.card + Eb.card ≤ 2 * s - 1 at hab
  change Eb.card + Ec.card ≤ 2 * s - 1 at hbc
  change E2.card + Eb.card + Ec.card ≤ 3 * s - 2 at habc
  let ψ : G.edgeSet → ℕ := fun e =>
    if h2 : e.val ∈ E2 then
      (E2.equivFin ⟨e.val, h2⟩).val + 1
    else if hbe : e.val ∈ Eb then
      (if a = s then 2 else 1) + (Eb.equivFin ⟨e.val, hbe⟩).val
    else if hce : e.val ∈ Ec then
      (s - c + 1) + (Ec.equivFin ⟨e.val, hce⟩).val
    else 1
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro v
    rcases hφ v with h | h <;> omega
  · intro e
    have hmem : ∀ r, e.val ∈ simple_graph_endpoint_sum_edges G φ r ↔
      Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e.val = r := by
      intro r
      rw [simple_graph_endpoint_sum_edges, Finset.mem_filter]
      simp [e.2]
    have hpart : Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e.val = 2 ∨
                 Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e.val = s + 1 ∨
                 Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e.val = 2 * s := by
      rcases e with ⟨⟨u, v⟩, he⟩
      dsimp
      rcases hφ u with hu | hu <;> rcases hφ v with hv | hv
      · left; rw [hu, hv]
      · right; left; rw [hu, hv, add_comm]
      · right; left; rw [hu, hv]
      · right; right; rw [hu, hv, two_mul]
    rcases hpart with hL2 | hLb | hLc
    · have h2 : e.val ∈ E2 := (hmem 2).mpr hL2
      dsimp [ψ]
      rw [dif_pos h2]
      have hi := (E2.equivFin ⟨e.val, h2⟩).isLt
      omega
    · have hb_mem : e.val ∈ Eb := (hmem (s + 1)).mpr hLb
      have hnot2 : e.val ∉ E2 := by
        intro h2
        have := (hmem 2).mp h2
        omega
      dsimp [ψ]
      rw [dif_neg hnot2, dif_pos hb_mem]
      have hj := (Eb.equivFin ⟨e.val, hb_mem⟩).isLt
      dsimp [a]
      split_ifs <;> omega
    · have hc_mem : e.val ∈ Ec := (hmem (2 * s)).mpr hLc
      have hnot2 : e.val ∉ E2 := by
        intro h2
        have := (hmem 2).mp h2
        omega
      have hnotb : e.val ∉ Eb := by
        intro hbe
        have := (hmem (s + 1)).mp hbe
        omega
      dsimp [ψ]
      rw [dif_neg hnot2, dif_neg hnotb, dif_pos hc_mem]
      have hk := (Ec.equivFin ⟨e.val, hc_mem⟩).isLt
      dsimp [c]
      omega
  · intro e₁ e₂ heq
    let L (e : G.edgeSet) : ℕ := Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e.val
    have hmem : ∀ (e : G.edgeSet) r, e.val ∈ simple_graph_endpoint_sum_edges G φ r ↔ L e = r := by
      intro e r
      rw [simple_graph_endpoint_sum_edges, Finset.mem_filter]
      simp [e.2, L]
    have hpart : ∀ e : G.edgeSet, L e = 2 ∨ L e = s + 1 ∨ L e = 2 * s := by
      intro e
      rcases e with ⟨⟨u, v⟩, he⟩
      dsimp [L]
      rcases hφ u with hu | hu <;> rcases hφ v with hv | hv
      · left; rw [hu, hv]
      · right; left; rw [hu, hv, add_comm]
      · right; left; rw [hu, hv]
      · right; right; rw [hu, hv, two_mul]
    have hprops : ∀ e : G.edgeSet,
      (L e = 2 ∧ ∃ h2 : e.val ∈ E2, L e + ψ e = 3 + (E2.equivFin ⟨e.val, h2⟩).val ∧ L e + ψ e ≤ a + 2) ∨
      (L e = s + 1 ∧ ∃ hb : e.val ∈ Eb,
        L e + ψ e = s + 1 + (if a = s then 2 else 1) + (Eb.equivFin ⟨e.val, hb⟩).val ∧
        a + 2 < L e + ψ e ∧ L e + ψ e ≤ 3 * s - c) ∨
      (L e = 2 * s ∧ ∃ hc : e.val ∈ Ec,
        L e + ψ e = 3 * s - c + 1 + (Ec.equivFin ⟨e.val, hc⟩).val ∧ 3 * s - c < L e + ψ e) := by
      intro e
      rcases hpart e with h2 | hb | hc
      · left
        have h2_mem : e.val ∈ E2 := (hmem e 2).mpr h2
        refine ⟨h2, h2_mem, ?_, ?_⟩
        · dsimp [ψ]
          rw [dif_pos h2_mem, h2]
          omega
        · dsimp [ψ]
          rw [dif_pos h2_mem, h2]
          have := (E2.equivFin ⟨e.val, h2_mem⟩).isLt
          omega
      · right; left
        have hb_mem : e.val ∈ Eb := (hmem e (s + 1)).mpr hb
        have hnot2 : e.val ∉ E2 := by
          intro h
          have := (hmem e 2).mp h
          omega
        refine ⟨hb, hb_mem, ?_, ?_⟩
        · dsimp [ψ]
          rw [dif_neg hnot2, dif_pos hb_mem, hb]
          omega
        · dsimp [ψ]
          rw [dif_neg hnot2, dif_pos hb_mem, hb]
          have hj := (Eb.equivFin ⟨e.val, hb_mem⟩).isLt
          dsimp [a, c]
          split_ifs <;> omega
      · right; right
        have hc_mem : e.val ∈ Ec := (hmem e (2 * s)).mpr hc
        have hnot2 : e.val ∉ E2 := by
          intro h
          have := (hmem e 2).mp h
          omega
        have hnotb : e.val ∉ Eb := by
          intro h
          have := (hmem e (s + 1)).mp h
          omega
        refine ⟨hc, hc_mem, ?_, ?_⟩
        · dsimp [ψ]
          rw [dif_neg hnot2, dif_neg hnotb, dif_pos hc_mem, hc]
          omega
        · dsimp [ψ]
          rw [dif_neg hnot2, dif_neg hnotb, dif_pos hc_mem, hc]
          omega
    change L e₁ + ψ e₁ = L e₂ + ψ e₂ at heq
    rcases hprops e₁ with ⟨hL1, h2_1, heq1, hbound1⟩ | ⟨hL1, hb_1, heq1, hbound1_lo, hbound1_hi⟩ | ⟨hL1, hc_1, heq1, hbound1⟩
    · rcases hprops e₂ with ⟨hL2, h2_2, heq2, hbound2⟩ | ⟨hL2, hb_2, heq2, hbound2_lo, hbound2_hi⟩ | ⟨hL2, hc_2, heq2, hbound2⟩
      · have hval : (E2.equivFin ⟨e₁.val, h2_1⟩).val = (E2.equivFin ⟨e₂.val, h2_2⟩).val := by omega
        have heq_val := admissibility_lemma_sufficiency_equivFin_val_inj E2 e₁.val e₂.val h2_1 h2_2 hval
        exact Subtype.ext heq_val
      · omega
      · omega
    · rcases hprops e₂ with ⟨hL2, h2_2, heq2, hbound2⟩ | ⟨hL2, hb_2, heq2, hbound2_lo, hbound2_hi⟩ | ⟨hL2, hc_2, heq2, hbound2⟩
      · omega
      · have hval : (Eb.equivFin ⟨e₁.val, hb_1⟩).val = (Eb.equivFin ⟨e₂.val, hb_2⟩).val := by omega
        have heq_val := admissibility_lemma_sufficiency_equivFin_val_inj Eb e₁.val e₂.val hb_1 hb_2 hval
        exact Subtype.ext heq_val
      · omega
    · rcases hprops e₂ with ⟨hL2, h2_2, heq2, hbound2⟩ | ⟨hL2, hb_2, heq2, hbound2_lo, hbound2_hi⟩ | ⟨hL2, hc_2, heq2, hbound2⟩
      · omega
      · omega
      · have hval : (Ec.equivFin ⟨e₁.val, hc_1⟩).val = (Ec.equivFin ⟨e₂.val, hc_2⟩).val := by omega
        have heq_val := admissibility_lemma_sufficiency_equivFin_val_inj Ec e₁.val e₂.val hc_1 hc_2 hval
        exact Subtype.ext heq_val
