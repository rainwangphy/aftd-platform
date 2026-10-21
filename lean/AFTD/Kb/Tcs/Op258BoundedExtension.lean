import AFTD.Prelude
import AFTD.Kb.Tcs.Op258ExistsFinsetSumGtOne
import AFTD.Kb.Tcs.Op258Bounded
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op_258_bounded_extension

Topic: combinatorics   Node: e0279b2d674b

Provenance: helper lemma. step towards op_258_forces_step

For a positive antitone profile a with Σ a i > 1 there is n₀ such that for every n ≥ n₀, every partially defined a-bounded colouring of the edges of K_n (i.e. the coloured edge set s has fibres of size at most a i * C(n,2)) extends to a full a-bounded colouring of all edges of K_n agreeing with it on s.
-/

lemma op_258_bounded_extension_exists_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (I : Finset ℕ+) : ∀ (cap : ℕ+ → ℕ) (T : Finset V),
    T.card ≤ ∑ i ∈ I, cap i →
    ∃ f : V → ℕ+, ∀ i : ℕ+, (T.filter (fun e => f e = i)).card ≤ cap i := by
  classical
  intro cap T
  induction T using Finset.induction generalizing cap with
  | empty =>
      intro _
      exact ⟨fun _ => 1, fun i => by simp⟩
  | insert x T hx ih =>
      intro h
      have hpos : 0 < ∑ i ∈ I, cap i := by
        have hc : (insert x T).card = T.card + 1 := Finset.card_insert_of_notMem hx
        omega
      have hex : ∃ i ∈ I, 0 < cap i := by
        by_contra hcon
        have hz : ∀ i ∈ I, cap i = 0 := by
          intro i hi
          rcases Nat.eq_zero_or_pos (cap i) with h' | h'
          · exact h'
          · exact absurd ⟨i, hi, h'⟩ hcon
        have : ∑ i ∈ I, cap i = 0 := Finset.sum_eq_zero hz
        omega
      obtain ⟨i₀, hi₀mem, hi₀pos⟩ := hex
      set cap' : ℕ+ → ℕ := Function.update cap i₀ (cap i₀ - 1) with hcap'def
      have hsum' : T.card ≤ ∑ i ∈ I, cap' i := by
        have hsub : I \ {i₀} = I.erase i₀ := Finset.sdiff_singleton_eq_erase i₀ I
        rw [hcap'def, Finset.sum_update_of_mem hi₀mem, hsub]
        have hkey : cap i₀ + ∑ x ∈ I.erase i₀, cap x = ∑ x ∈ I, cap x :=
          Finset.add_sum_erase I cap hi₀mem
        have hc : (insert x T).card = T.card + 1 := Finset.card_insert_of_notMem hx
        omega
      obtain ⟨f', hf'⟩ := ih cap' hsum'
      refine ⟨Function.update f' x i₀, ?_⟩
      intro i
      by_cases hii : i = i₀
      · subst i
        have hfil : (insert x T).filter (fun e => Function.update f' x i₀ e = i₀)
            = insert x (T.filter (fun e => Function.update f' x i₀ e = i₀)) := by
          rw [Finset.filter_insert]
          simp
        have hcongr : T.filter (fun e => Function.update f' x i₀ e = i₀)
            = T.filter (fun e => f' e = i₀) := by
          apply Finset.filter_congr
          intro e he
          have hne : e ≠ x := fun h' => hx (h' ▸ he)
          rw [Function.update_of_ne hne]
        rw [hfil, hcongr, Finset.card_insert_of_notMem (by simp [hx])]
        have h2 : cap' i₀ = cap i₀ - 1 := by rw [hcap'def, Function.update_self]
        have h1 : (T.filter (fun e => f' e = i₀)).card ≤ cap i₀ - 1 := h2 ▸ hf' i₀
        omega
      · have hne : i₀ ≠ i := fun h' => hii h'.symm
        have hfil : (insert x T).filter (fun e => Function.update f' x i₀ e = i)
            = T.filter (fun e => Function.update f' x i₀ e = i) := by
          rw [Finset.filter_insert]
          simp [hne]
        have hcongr : T.filter (fun e => Function.update f' x i₀ e = i)
            = T.filter (fun e => f' e = i) := by
          apply Finset.filter_congr
          intro e he
          have hne' : e ≠ x := fun h' => hx (h' ▸ he)
          rw [Function.update_of_ne hne']
        have h2 : cap' i = cap i := by
          rw [hcap'def]; exact Function.update_of_ne hii (cap i₀ - 1) cap
        rw [hfil, hcongr]
        exact h2 ▸ hf' i

/-- Partial a-bounded colourings of K_n extend to full a-bounded colourings for all large n. -/
theorem op_258_bounded_extension (a : ℕ+ → ℝ) (hpos : ∀ i, 0 < a i) (hanti : Antitone a)
    (hsum : 1 < ∑' i : ℕ+, ENNReal.ofReal (a i)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (s : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet)
      (c₀ : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+),
      (∀ i : ℕ+, ((s.filter (fun e => c₀ e = i)).card : ℝ) ≤ a i * (n.choose 2 : ℝ)) →
      ∃ c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+,
        op_258_bounded a n c ∧ ∀ e ∈ s, c e = c₀ e := by
  classical
  obtain ⟨I, δ, hδ, hIsum⟩ := op_258_exists_finset_sum_gt_one a (fun i => (hpos i).le) hsum
  obtain ⟨N, hN⟩ := exists_nat_ge ((I.card : ℝ) / δ)
  refine ⟨2 * N + 2, ?_⟩
  intro n hn s c₀ hc₀
  have hcardE : (Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).card
      = n.choose 2 := by
    rw [SimpleGraph.edgeSet_univ_card, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp
  have hIcast : (I.card : ℝ) ≤ δ * (n.choose 2 : ℝ) := by
    have h1 : (I.card : ℝ) ≤ δ * N := by
      rw [div_le_iff₀ hδ] at hN
      linarith
    have h2 : (N : ℝ) ≤ (n.choose 2 : ℝ) := by
      have hnc : ((n.choose 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ n
      have hn' : (2 * (N:ℝ) + 2) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [hnc]
      nlinarith
    nlinarith [hδ.le]
  set cap : ℕ+ → ℕ := fun i =>
    if i ∈ I then Nat.floor (a i * (n.choose 2 : ℝ)) - (s.filter (fun e => c₀ e = i)).card else 0
    with hcapdef
  have hcap_eq : ∀ i ∈ I, (cap i : ℝ) =
      (Nat.floor (a i * (n.choose 2 : ℝ)) : ℝ) - ((s.filter (fun e => c₀ e = i)).card : ℝ) := by
    intro i hi
    have hle : (s.filter (fun e => c₀ e = i)).card ≤ Nat.floor (a i * (n.choose 2 : ℝ)) :=
      Nat.le_floor (hc₀ i)
    simp only [hcapdef, if_pos hi]
    push_cast [hle]
    ring
  have hsum_card : (Finset.univ \ s).card ≤ ∑ i ∈ I, cap i := by
    have hR : ((Finset.univ \ s).card : ℝ) ≤ ((∑ i ∈ I, cap i : ℕ) : ℝ) := by
      have hs_card : ((Finset.univ \ s).card : ℝ) = (n.choose 2 : ℝ) - (s.card : ℝ) := by
        have h1 : (Finset.univ \ s : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).card
            = n.choose 2 - s.card := by
          rw [Finset.card_sdiff, Finset.inter_univ, hcardE]
        rw [h1]
        have h2 : s.card ≤ n.choose 2 := by rw [← hcardE]; exact Finset.card_le_univ s
        rw [Nat.cast_sub h2]
      have hfloor_lb : (∑ i ∈ I, (Nat.floor (a i * (n.choose 2 : ℝ)) : ℝ))
          ≥ (1 + δ) * (n.choose 2 : ℝ) - (I.card : ℝ) := by
        have h1 : ∀ i ∈ I, (Nat.floor (a i * (n.choose 2 : ℝ)) : ℝ)
            ≥ a i * (n.choose 2 : ℝ) - 1 := by
          intro i _
          have h3 := Nat.lt_floor_add_one (a i * (n.choose 2 : ℝ))
          linarith
        have h2 : (∑ i ∈ I, (a i * (n.choose 2 : ℝ) - 1))
            = (∑ i ∈ I, a i) * (n.choose 2 : ℝ) - (I.card : ℝ) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
          simp
        have h3 : (1 + δ) * (n.choose 2 : ℝ) ≤ (∑ i ∈ I, a i) * (n.choose 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right hIsum (Nat.cast_nonneg _)
        calc (∑ i ∈ I, (Nat.floor (a i * (n.choose 2 : ℝ)) : ℝ))
            ≥ ∑ i ∈ I, (a i * (n.choose 2 : ℝ) - 1) := Finset.sum_le_sum h1
          _ = (∑ i ∈ I, a i) * (n.choose 2 : ℝ) - (I.card : ℝ) := h2
          _ ≥ (1 + δ) * (n.choose 2 : ℝ) - (I.card : ℝ) := by linarith
      have hsi_le : (∑ i ∈ I, ((s.filter (fun e => c₀ e = i)).card : ℝ)) ≤ (s.card : ℝ) := by
        have hnat : ∑ i ∈ I, (s.filter (fun e => c₀ e = i)).card ≤ s.card := by
          have hpb : (↑I : Set ℕ+).PairwiseDisjoint (fun i => s.filter (fun e => c₀ e = i)) := by
            intro i _ j _ hij
            refine Finset.disjoint_left.mpr ?_
            intro e he he'
            simp only [Finset.mem_filter] at he he'
            exact hij (by rw [← he.2, ← he'.2])
          rw [← Finset.card_biUnion hpb]
          exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun i _ => Finset.filter_subset _ _))
        calc (∑ i ∈ I, ((s.filter (fun e => c₀ e = i)).card : ℝ))
            = ((∑ i ∈ I, (s.filter (fun e => c₀ e = i)).card : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (s.card : ℝ) := by exact_mod_cast hnat
      have hsum_eq : ((∑ i ∈ I, cap i : ℕ) : ℝ)
          = (∑ i ∈ I, (Nat.floor (a i * (n.choose 2 : ℝ)) : ℝ))
            - (∑ i ∈ I, ((s.filter (fun e => c₀ e = i)).card : ℝ)) := by
        push_cast
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl hcap_eq
      rw [hs_card, hsum_eq]
      nlinarith [hfloor_lb, hsi_le, hIcast]
    exact_mod_cast hR
  obtain ⟨f, hf⟩ := op_258_bounded_extension_exists_coloring I cap (Finset.univ \ s) hsum_card
  refine ⟨fun e => if e ∈ s then c₀ e else f e, ?_, ?_⟩
  · intro i
    have hsplit : (Finset.univ.filter (fun e => (if e ∈ s then c₀ e else f e) = i))
        = s.filter (fun e => c₀ e = i) ∪ (Finset.univ \ s).filter (fun e => f e = i) := by
      ext e
      by_cases he : e ∈ s <;> simp [he]
    have hcard : (Finset.univ.filter (fun e => (if e ∈ s then c₀ e else f e) = i)).card
        = (s.filter (fun e => c₀ e = i)).card
          + ((Finset.univ \ s).filter (fun e => f e = i)).card := by
      rw [hsplit]
      have hdisj : Disjoint (s.filter (fun e => c₀ e = i))
          ((Finset.univ \ s).filter (fun e => f e = i)) := by
        rw [Finset.disjoint_left]
        intro e he he'
        simp only [Finset.mem_filter] at he he'
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at he'
        exact he'.1 he.1
      rw [Finset.card_union_of_disjoint hdisj]
    rw [hcard]
    push_cast
    by_cases hiI : i ∈ I
    · have hcap : cap i = Nat.floor (a i * (n.choose 2 : ℝ))
          - (s.filter (fun e => c₀ e = i)).card := by simp only [hcapdef, if_pos hiI]
      have hle : (s.filter (fun e => c₀ e = i)).card ≤ Nat.floor (a i * (n.choose 2 : ℝ)) :=
        Nat.le_floor (hc₀ i)
      have hfib : ((Finset.univ \ s).filter (fun e => f e = i)).card ≤ cap i := hf i
      rw [hcap] at hfib
      have hnat : (s.filter (fun e => c₀ e = i)).card
          + ((Finset.univ \ s).filter (fun e => f e = i)).card
          ≤ Nat.floor (a i * (n.choose 2 : ℝ)) := by
        calc (s.filter (fun e => c₀ e = i)).card
              + ((Finset.univ \ s).filter (fun e => f e = i)).card
            ≤ (s.filter (fun e => c₀ e = i)).card
              + (Nat.floor (a i * (n.choose 2 : ℝ)) - (s.filter (fun e => c₀ e = i)).card) :=
                Nat.add_le_add_left hfib _
          _ = Nat.floor (a i * (n.choose 2 : ℝ)) := Nat.add_sub_of_le hle
      have hnatR : ((s.filter (fun e => c₀ e = i)).card : ℝ)
          + (((Finset.univ \ s).filter (fun e => f e = i)).card : ℝ)
          ≤ (Nat.floor (a i * (n.choose 2 : ℝ)) : ℝ) := by
        exact_mod_cast hnat
      have hfloor : (Nat.floor (a i * (n.choose 2 : ℝ)) : ℝ) ≤ a i * (n.choose 2 : ℝ) :=
        Nat.floor_le (mul_nonneg (hpos i).le (Nat.cast_nonneg _))
      linarith
    · have hcap : cap i = 0 := by simp only [hcapdef, if_neg hiI]
      have hfib : ((Finset.univ \ s).filter (fun e => f e = i)).card ≤ cap i := hf i
      rw [hcap] at hfib
      have hfib0 : ((Finset.univ \ s).filter (fun e => f e = i)).card = 0 := Nat.le_zero.mp hfib
      simp only [hfib0, Nat.cast_zero, add_zero]
      exact hc₀ i
  · intro e he
    simp [he]
