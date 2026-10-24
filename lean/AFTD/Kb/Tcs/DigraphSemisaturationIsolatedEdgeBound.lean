import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSsat
import AFTD.Kb.Tcs.DigraphIsOriented
import AFTD.Kb.Tcs.DigraphHasIsolatedEdge
import AFTD.Kb.Tcs.DigraphEdgeCount
import AFTD.Kb.Tcs.DigraphIsSemisaturating

/-!
# digraph_semisaturation_isolated_edge_bound

Topic: graphs   Node: e2f7fbb8a3f2

Provenance: helper lemma. arXiv:2610.18600 Lemma 2.1

If G : Digraph V is a finite oriented digraph with DecidableEq V and DecidableRel G.Adj satisfying digraph_is_oriented G and digraph_has_isolated_edge G, then there exists n₀ : ℕ such that for all n ≥ n₀, digraph_ssat n G ≤ 3 * (digraph_edge_count G - 1).
-/

/-- Upper bound 3(|E(G)| - 1) on ssat(n, G) for oriented graphs containing an isolated edge. -/
theorem digraph_semisaturation_isolated_edge_bound {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (hG : digraph_is_oriented G) (he : digraph_has_isolated_edge G) : ∃ n₀ : ℕ, ∀ n ≥ n₀, digraph_ssat n G ≤ 3 * (digraph_edge_count G - 1) := by
  obtain ⟨u, v, huv, hiso⟩ := he
  use 3 * Fintype.card V
  intro n hn
  have hcard_le : Fintype.card (Fin 3 × V) ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    exact hn
  obtain ⟨ι⟩ : Nonempty (Fin 3 × V ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le hcard_le
  let E' := (Finset.univ.filter fun p : V × V => G.Adj p.1 p.2).erase (u, v)
  let H : Digraph (Fin n) := ⟨fun x y => ∃ i : Fin 3, ∃ p ∈ E', x = ι (i, p.1) ∧ y = ι (i, p.2)⟩
  have hd : DecidableRel H.Adj := Classical.decRel _
  have h_semi : digraph_is_semisaturating H G := by
    refine ⟨?_, ?_⟩
    · intro x y hxy hyx
      rcases hxy with ⟨i, p, hp, rfl, rfl⟩
      rcases hyx with ⟨j, q, hq, hy, hx⟩
      have hq2 : (j, q.2) = (i, p.1) := ι.injective hx.symm
      have hq1 : (j, q.1) = (i, p.2) := ι.injective hy.symm
      have hp_adj : G.Adj p.1 p.2 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2
      have hq_adj : G.Adj q.1 q.2 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hq)).2
      injection hq1 with _ hq1_val
      injection hq2 with _ hq2_val
      rw [hq1_val, hq2_val] at hq_adj
      exact hG p.1 p.2 hp_adj hq_adj
    · intro x y hxy _ _
      have hloop (z : V) : ¬ G.Adj z z := fun h => hG z z h h
      have huv_ne : u ≠ v := by
        rintro rfl
        exact hloop u huv
      obtain ⟨i, hx, hy⟩ : ∃ i : Fin 3, (∀ w, ι (i, w) ≠ x) ∧ (∀ w, ι (i, w) ≠ y) := by
        have h_inj (i j : Fin 3) (w₁ w₂ : V) (h : ι (i, w₁) = ι (j, w₂)) : i = j := by
          have := ι.injective h
          exact congr_arg Prod.fst this
        have h_not_both (i j : Fin 3) (hij : i ≠ j) (z : Fin n) :
            (∃ w, ι (i, w) = z) → (∃ w, ι (j, w) = z) → False := by
          rintro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩
          have : i = j := h_inj i j w₁ w₂ (hw₁.trans hw₂.symm)
          exact hij this
        let i0 : Fin 3 := 0
        let i1 : Fin 3 := 1
        let i2 : Fin 3 := 2
        have h01 : i0 ≠ i1 := by decide
        have h02 : i0 ≠ i2 := by decide
        have h12 : i1 ≠ i2 := by decide
        by_cases h0 : (∀ w, ι (i0, w) ≠ x) ∧ (∀ w, ι (i0, w) ≠ y)
        · exact ⟨i0, h0⟩
        by_cases h1 : (∀ w, ι (i1, w) ≠ x) ∧ (∀ w, ι (i1, w) ≠ y)
        · exact ⟨i1, h1⟩
        by_cases h2 : (∀ w, ι (i2, w) ≠ x) ∧ (∀ w, ι (i2, w) ≠ y)
        · exact ⟨i2, h2⟩
        exfalso
        rw [not_and_or] at h0 h1 h2
        push Not at h0 h1 h2
        rcases h0 with h0x | h0y <;> rcases h1 with h1x | h1y <;> rcases h2 with h2x | h2y
        · exact h_not_both i0 i1 h01 x h0x h1x
        · exact h_not_both i0 i1 h01 x h0x h1x
        · exact h_not_both i0 i2 h02 x h0x h2x
        · exact h_not_both i1 i2 h12 y h1y h2y
        · exact h_not_both i1 i2 h12 x h1x h2x
        · exact h_not_both i0 i2 h02 y h0y h2y
        · exact h_not_both i0 i1 h01 y h0y h1y
        · exact h_not_both i0 i1 h01 y h0y h1y
      let f : V → Fin n := fun w => if w = u then x else if w = v then y else ι (i, w)
      have hfu : f u = x := if_pos rfl
      have hfv : f v = y := by
        dsimp [f]
        rw [if_neg huv_ne.symm, if_pos rfl]
      have hfinj : Function.Injective f := by
        intro a b hab
        dsimp only [f] at hab
        split_ifs at hab with h1 h2 h3 h4 h5 <;> try (subst_vars; rfl)
        all_goals
          first
          | exact False.elim (hxy hab)
          | exact False.elim (hxy hab.symm)
          | exact False.elim (hx _ hab)
          | exact False.elim (hx _ hab.symm)
          | exact False.elim (hy _ hab)
          | exact False.elim (hy _ hab.symm)
          | have := ι.injective hab; aesop
      refine ⟨f, hfinj, ?_, ⟨u, v, huv, hfu, hfv⟩⟩
      intro a b hab
      by_cases hab_eq : (a, b) = (u, v)
      · have ha : a = u := congr_arg Prod.fst hab_eq
        have hb : b = v := congr_arg Prod.snd hab_eq
        right
        rw [ha, hb, hfu, hfv]
        exact ⟨rfl, rfl⟩
      · left
        have ha_ne_u : a ≠ u := by
          intro ha
          have hab' : G.Adj u b := ha ▸ hab
          have : b = u ∨ b = v := hiso b (Or.inl hab')
          cases this with
          | inl h1 => exact hloop u (h1 ▸ hab')
          | inr h2 => exact hab_eq (Prod.ext ha h2)
        have ha_ne_v : a ≠ v := by
          intro ha
          have hab' : G.Adj v b := ha ▸ hab
          have : b = u ∨ b = v := hiso b (Or.inr (Or.inr (Or.inl hab')))
          cases this with
          | inl h1 => exact hG u v huv (h1 ▸ hab')
          | inr h2 => exact hloop v (h2 ▸ hab')
        have hb_ne_u : b ≠ u := by
          intro hb
          have hab' : G.Adj a u := hb ▸ hab
          have : a = u ∨ a = v := hiso a (Or.inr (Or.inl hab'))
          cases this with
          | inl h1 => exact hloop u (h1 ▸ hab')
          | inr h2 => exact hG u v huv (h2 ▸ hab')
        have hb_ne_v : b ≠ v := by
          intro hb
          have hab' : G.Adj a v := hb ▸ hab
          have : a = u ∨ a = v := hiso a (Or.inr (Or.inr (Or.inr hab')))
          cases this with
          | inl h1 => exact hab_eq (Prod.ext h1 hb)
          | inr h2 => exact hloop v (h2 ▸ hab')
        have hfa : f a = ι (i, a) := by
          dsimp [f]
          rw [if_neg ha_ne_u, if_neg ha_ne_v]
        have hfb : f b = ι (i, b) := by
          dsimp [f]
          rw [if_neg hb_ne_u, if_neg hb_ne_v]
        rw [hfa, hfb]
        refine ⟨i, (a, b), ?_, rfl, rfl⟩
        rw [Finset.mem_erase, Finset.mem_filter]
        exact ⟨hab_eq, Finset.mem_univ _, hab⟩
  have h_count : digraph_edge_count H ≤ 3 * (digraph_edge_count G - 1) := by
    have hE' : E'.card = digraph_edge_count G - 1 := by
      have : (u, v) ∈ Finset.univ.filter fun p : V × V => G.Adj p.1 p.2 := by
        simp [huv]
      rw [Finset.card_erase_of_mem this]
      rfl
    have hsub : (Finset.univ.filter fun p : Fin n × Fin n => H.Adj p.1 p.2) ⊆
        ((Finset.univ : Finset (Fin 3)) ×ˢ E').image (fun ip => (ι (ip.1, ip.2.1), ι (ip.1, ip.2.2))) := by
      intro ⟨x, y⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rcases hmem with ⟨i, p, hp, rfl, rfl⟩
      rw [Finset.mem_image]
      exact ⟨(i, p), Finset.mem_product.mpr ⟨Finset.mem_univ i, hp⟩, rfl⟩
    have hle1 : (Finset.univ.filter fun p : Fin n × Fin n => H.Adj p.1 p.2).card ≤
        (((Finset.univ : Finset (Fin 3)) ×ˢ E').image (fun ip => (ι (ip.1, ip.2.1), ι (ip.1, ip.2.2)))).card :=
      Finset.card_le_card hsub
    have hle2 : (((Finset.univ : Finset (Fin 3)) ×ˢ E').image (fun ip => (ι (ip.1, ip.2.1), ι (ip.1, ip.2.2)))).card ≤
        ((Finset.univ : Finset (Fin 3)) ×ˢ E').card := Finset.card_image_le
    have hcard : ((Finset.univ : Finset (Fin 3)) ×ˢ E').card = 3 * (digraph_edge_count G - 1) := by
      rw [Finset.card_product]
      simp [hE']
    change (Finset.univ.filter fun p : Fin n × Fin n => H.Adj p.1 p.2).card ≤ 3 * (digraph_edge_count G - 1)
    omega
  have h_ssat_le : digraph_ssat n G ≤ digraph_edge_count H := by
    unfold digraph_ssat
    apply Nat.sInf_le
    exact ⟨H, hd, h_semi, rfl⟩
  exact h_ssat_le.trans h_count
