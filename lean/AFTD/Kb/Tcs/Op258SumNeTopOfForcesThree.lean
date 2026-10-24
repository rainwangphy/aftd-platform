import AFTD.Prelude
import AFTD.Kb.Tcs.Op258Forces
import AFTD.Kb.Tcs.Op258NoMonoTriangleOfLayering
import AFTD.Kb.Tcs.Op258HypercubeBipartiteDecomposition
import AFTD.Kb.Tcs.Op258ExistsDivergentCapacityCovering
import AFTD.Kb.Tcs.Op258Bounded
import AFTD.Kb.Tcs.Op258HasMonoClique
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_258_sum_ne_top_of_forces_three

Topic: combinatorics   Node: 9c36cb0c1e8f

Provenance: helper lemma. step towards op_258_forces_step

If a positive antitone profile a forces a monochromatic triangle K_3 on sufficiently large complete graphs, then the infinite sum of a_i in ENNReal is finite.
-/

lemma op_258_sum_ne_top_of_forces_three_greedy_colouring {X : Type*} [DecidableEq X] :
    ∀ (E : Finset X) (s : Finset ℕ+) (cap : ℕ+ → ℕ),
      E.card ≤ ∑ i ∈ s, cap i →
      ∃ c : X → ℕ+, (∀ e ∈ E, c e ∈ s) ∧ ∀ i, (E.filter (fun e => c e = i)).card ≤ cap i := by
  intro E
  induction E using Finset.induction_on with
  | empty =>
      intro s cap h
      refine ⟨fun _ => 1, ?_, ?_⟩
      · intro x hx; simp at hx
      · intro i; simp
  | insert a E ha ih =>
      intro s cap h
      have hcard : (insert a E).card = E.card + 1 := Finset.card_insert_of_notMem ha
      have hE : E.card ≤ ∑ i ∈ s, cap i := by omega
      obtain ⟨c, hcs, hcf⟩ := ih s cap hE
      have hmaps : (E : Set X).MapsTo c (s : Set ℕ+) := fun x hx => hcs x hx
      have hfib := Finset.card_eq_sum_card_fiberwise hmaps
      have hslack : ∃ i ∈ s, (E.filter (fun x => c x = i)).card < cap i := by
        by_contra hcon
        simp only [not_exists, not_and, not_lt] at hcon
        have h1 : ∑ i ∈ s, cap i ≤ ∑ i ∈ s, (E.filter (fun x => c x = i)).card :=
          Finset.sum_le_sum hcon
        omega
      obtain ⟨i₀, hi₀s, hi₀⟩ := hslack
      set c' : X → ℕ+ := fun x => if x = a then i₀ else c x with hc'
      have hca : c' a = i₀ := by simp [hc']
      have hon : ∀ x ∈ E, c' x = c x := by
        intro x hx
        have hxa : ¬ (x = a) := by rintro rfl; exact ha hx
        simp only [hc', if_neg hxa]
      refine ⟨c', ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with hx | hx
        · rw [hx, hca]; exact hi₀s
        · rw [hon x hx]; exact hcs x hx
      · intro i
        by_cases hii : i = i₀
        · have hmem : (insert a E).filter (fun x => c' x = i) =
              insert a (E.filter (fun x => c x = i₀)) := by
            rw [hii]
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hx, hcx⟩
              rcases hx with hx | hx
              · exact Or.inl hx
              · exact Or.inr ⟨hx, hon x hx ▸ hcx⟩
            · rintro (rfl | ⟨hx, hcx⟩)
              · exact ⟨Or.inl rfl, by simp [hc']⟩
              · exact ⟨Or.inr hx, hon x hx ▸ hcx⟩
          rw [hmem, Finset.card_insert_of_notMem (by simp [ha]), hii]
          omega
        · have hmem : (insert a E).filter (fun x => c' x = i) = E.filter (fun x => c x = i) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hx, hcx⟩
              rcases hx with hx | hx
              · rw [hx, hca] at hcx
                exact absurd hcx (Ne.symm hii)
              · exact ⟨hx, hon x hx ▸ hcx⟩
            · rintro ⟨hx, hcx⟩
              exact ⟨Or.inr hx, (hon x hx).symm ▸ hcx⟩
          rw [hmem]
          exact hcf i

/-- Any positive antitone profile that forces a monochromatic triangle K_3 has finite ENNReal sum (Theorem 1.3 of Di Braccio et al.). -/
theorem op_258_sum_ne_top_of_forces_three (a : ℕ+ → ℝ) (hpos : ∀ i, 0 < a i) (hanti : Antitone a)
    (h3 : op_258_forces a 3) : (∑' i : ℕ+, ENNReal.ofReal (a i)) ≠ ⊤ := by
  intro hsum
  obtain ⟨n₀, hn₀⟩ := h3
  obtain ⟨l, hl, I, cap, h2l, hdisj, hcaple, hlayersum⟩ :=
    op_258_exists_divergent_capacity_covering a hpos hanti hsum n₀
  obtain ⟨layer, f, hbip, hlayercard⟩ := op_258_hypercube_bipartite_decomposition l hl
  have hper : ∀ j : Fin l, ∃ c : ↥(SimpleGraph.completeGraph (Fin (2^l))).edgeSet → ℕ+,
      (∀ e ∈ Finset.univ.filter (fun e => layer e = j), c e ∈ I j) ∧
      ∀ i, ((Finset.univ.filter (fun e => layer e = j)).filter (fun e => c e = i)).card ≤ cap i := by
    intro j
    exact op_258_sum_ne_top_of_forces_three_greedy_colouring _ (I j) cap
      (le_trans (hlayercard j) (hlayersum j))
  choose cc hccmem hccfiber using hper
  let c : ↥(SimpleGraph.completeGraph (Fin (2^l))).edgeSet → ℕ+ := fun e => cc (layer e) e
  have hcmem : ∀ e, c e ∈ I (layer e) := by
    intro e
    exact hccmem (layer e) e (by simp)
  have huniq : ∀ (i : ℕ+) (j j' : Fin l), i ∈ I j → i ∈ I j' → j = j' := by
    intro i j j' hj hj'
    by_contra hne
    exact absurd hj' (Finset.disjoint_left.mp (hdisj j j' hne) hj)
  have hemp : ∀ i : ℕ+, ¬ (∃ j : Fin l, i ∈ I j) → Finset.univ.filter (fun e => c e = i) = ∅ := by
    intro i hi
    apply Finset.filter_false_of_mem
    intro e _ he
    exact hi ⟨layer e, he ▸ hcmem e⟩
  have hcf : ∀ i : ℕ+, (Finset.univ.filter (fun e => c e = i)).card ≤ cap i := by
    intro i
    by_cases hi : ∃ j : Fin l, i ∈ I j
    · obtain ⟨j, hij⟩ := hi
      have hEq : Finset.univ.filter (fun e => c e = i) =
          (Finset.univ.filter (fun e => layer e = j)).filter (fun e => cc j e = i) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hci
          have h2 : layer e = j := huniq i (layer e) j (hci ▸ hcmem e) hij
          refine ⟨h2, ?_⟩
          have h3 : cc j e = cc (layer e) e := by rw [h2]
          exact h3.trans hci
        · rintro ⟨h2, hci⟩
          have h3 : cc j e = cc (layer e) e := by rw [h2]
          exact h3.symm.trans hci
      rw [hEq]
      exact hccfiber j i
    · rw [hemp i hi]
      simp
  let col_layer : ℕ+ → Fin l := fun i => if h : ∃ j : Fin l, i ∈ I j then h.choose else ⟨0, hl⟩
  have hcol : ∀ e, col_layer (c e) = layer e := by
    intro e
    have hex : ∃ j : Fin l, c e ∈ I j := ⟨layer e, hcmem e⟩
    simp only [col_layer, dif_pos hex]
    exact huniq (c e) hex.choose (layer e) hex.choose_spec (hcmem e)
  have hbound : op_258_bounded a (2^l) c := by
    intro i
    have h1 : ({e | c e = i} : Finset _).card ≤ cap i := hcf i
    by_cases hi : ∃ j : Fin l, i ∈ I j
    · obtain ⟨j, hij⟩ := hi
      have h2 : (cap i : ℝ) ≤ a i * ((2^l).choose 2 : ℝ) := hcaple j i hij
      have h3 : (({e | c e = i} : Finset _).card : ℝ) ≤ (cap i : ℝ) := by exact_mod_cast h1
      exact le_trans h3 h2
    · have h0 : ({e | c e = i} : Finset _) = ∅ := hemp i hi
      rw [h0]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (le_of_lt (hpos i)) (by positivity)
  exact op_258_no_mono_triangle_of_layering (2^l) l layer f hbip c col_layer hcol
    (hn₀ (2^l) h2l c hbound)
