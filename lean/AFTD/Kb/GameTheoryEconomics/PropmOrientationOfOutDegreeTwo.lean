import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.EdgesBetween
import AFTD.Kb.GameTheoryEconomics.HasOutDegreeTwoOrientation
import AFTD.Kb.GameTheoryEconomics.IncidentEdges
import AFTD.Kb.GameTheoryEconomics.IsOrientation
import AFTD.Kb.GameTheoryEconomics.IsPropmOrientation
import AFTD.Kb.GameTheoryEconomics.OrientationMaximinValue
import AFTD.Kb.GameTheoryEconomics.OrientationPropShare
import AFTD.Kb.GameTheoryEconomics.PropmCutChoose
import AFTD.Kb.GameTheoryEconomics.PropmEdgesBetweenSymm
import AFTD.Kb.GameTheoryEconomics.PropmMemBetween
import AFTD.Kb.GameTheoryEconomics.PropmSumIncident
import AFTD.Kb.GameTheoryEconomics.PropmSumIteMem
import AFTD.Kb.GameTheoryEconomics.RelevantMinValue

/-!
# propm_orientation_of_out_degree_two

Topic: fair_division   Node: 71a606af2401

If the simple graph underlying a loopless multigraph has an orientation with every out-degree at most two, then for nonnegative additive valuations there is a PROPm orientation (with the PROPm slack taken over relevant items).
-/

/-- If the simple graph underlying a loopless multigraph has an orientation with every out-degree at most two, then for nonnegative additive valuations there is a PROPm orientation. -/
theorem propm_orientation_of_out_degree_two {m n : ℕ} (ends : Fin m → Fin n × Fin n)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (u : Fin n → Fin m → ℝ) (hu : ∀ i e, 0 ≤ u i e)
    (hT : has_out_degree_two_orientation ends) :
    ∃ σ, is_orientation ends σ ∧ is_propm_orientation ends u σ := by
  classical
  obtain ⟨T, hTe, hTd⟩ := hT
  -- `cut a b`: agent `a` cuts the parallel class `{a, b}`, agent `b` chooses.
  set cut : Fin n → Fin n → Prop := fun a b => T a b = true ∧ (T b a = true → a < b) with hcut
  have asymm : ∀ a b, cut a b → cut b a → False := by
    rintro a b ⟨h1, h2⟩ ⟨h3, h4⟩
    exact absurd (h2 h3) (not_lt.mpr (h4 h1).le)
  have cut_ne : ∀ a b, cut a b → a ≠ b := fun a b h hab => by
    subst hab; exact asymm a a h h
  have total : ∀ a b, a ≠ b → (T a b = true ∨ T b a = true) → cut a b ∨ cut b a := by
    intro a b hab h
    by_cases h1 : T a b = true <;> by_cases h2 : T b a = true
    · rcases lt_or_gt_of_ne hab with hl | hl
      · exact Or.inl ⟨h1, fun _ => hl⟩
      · exact Or.inr ⟨h2, fun _ => hl⟩
    · exact Or.inl ⟨h1, fun h => absurd h h2⟩
    · exact Or.inr ⟨h2, fun h => absurd h h1⟩
    · simp_all
  choose K hKsub hKc hKh using
    fun i j => propm_cut_choose (edges_between ends i j) (u i) (u j) (hu i)
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin m → Fin n, ∀ e, σ e =
      if cut (ends e).1 (ends e).2 then
        (if e ∈ K (ends e).1 (ends e).2 then (ends e).1 else (ends e).2)
      else (if e ∈ K (ends e).2 (ends e).1 then (ends e).2 else (ends e).1) :=
    ⟨_, fun _ => rfl⟩
  have horient : is_orientation ends σ := by
    intro e; rw [hσ e]; split_ifs <;> simp
  -- On the class `{i, j}` cut by `i`, agent `i` keeps exactly `K i j`.
  have key : ∀ i j e, cut i j → e ∈ edges_between ends i j →
      σ e = if e ∈ K i j then i else j := by
    intro i j e hc he
    simp only [edges_between, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with h | h
    · rw [hσ e, h]; exact if_pos hc
    · rw [hσ e, h]; exact if_neg (fun h' => asymm _ _ hc h')
  refine ⟨σ, horient, fun i => ?_⟩
  set d := orientation_maximin_value ends u σ i with hd
  have hd0 : 0 ≤ d := (Finset.le_fold_max 0).mpr (Or.inl le_rfl)
  have hdj : ∀ j, j ≠ i → relevant_min_value ends u σ i j ≤ d := fun j hj =>
    (Finset.le_fold_max _).mpr (Or.inr ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩, le_rfl⟩)
  have hval : additive_valuation (u i) (bundle_of σ i) =
      ∑ e ∈ incident_edges ends i, (if σ e = i then u i e else 0) := by
    rw [← Finset.sum_filter]
    unfold additive_valuation
    congr 1
    ext e
    simp only [bundle_of, incident_edges, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; refine ⟨?_, h⟩; rcases horient e with h' | h' <;> rw [h] at h' <;> simp [h']
    · exact fun h => h.2
  -- Per parallel class `{i, j}`: `v_i(class) - 2 v_i(π_i ∩ class) ≤ [i cuts] · d_i`.
  have hpair : ∀ j, ∑ e ∈ edges_between ends i j, (u i e - 2 * if σ e = i then u i e else 0) ≤
      if cut i j then d else 0 := by
    intro j
    set B := edges_between ends i j with hB
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    by_cases hc : cut i j
    · rw [if_pos hc]
      have hij := cut_ne _ _ hc
      have hs : ∑ e ∈ B, (if σ e = i then u i e else 0) = ∑ e ∈ K i j, u i e := by
        rw [← propm_sum_ite_mem B (K i j) (hKsub i j)]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [key i j e hc he]
        by_cases hk : e ∈ K i j <;> simp [hk, Ne.symm hij]
      rw [hs]
      by_cases hR : (bundle_of σ j ∩ incident_edges ends i).Nonempty
      · obtain ⟨g, hgR, hgeq⟩ := Finset.exists_mem_eq_inf' hR (u i)
        have hrm : relevant_min_value ends u σ i j = u i g := by
          rw [relevant_min_value, dif_pos hR, hgeq]
        rw [Finset.mem_inter] at hgR
        have hgj : σ g = j := by simpa [bundle_of] using hgR.1
        have hgB : g ∈ B := propm_mem_between ends σ horient hgR.2 hgj hij
        have hgK : g ∉ K i j := by
          intro hk; rw [key i j g hc hgB, if_pos hk] at hgj; exact hij hgj
        have h1 := hKc i j g (Finset.mem_sdiff.mpr ⟨hgB, hgK⟩)
        have h2 := hdj j (Ne.symm hij)
        linarith
      · have hsub : B ⊆ K i j := by
          intro g hgB
          by_contra hgK
          apply hR
          refine ⟨g, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
          · simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [key i j g hc hgB, if_neg hgK]
          · simp only [hB, edges_between, Finset.mem_filter, Finset.mem_univ, true_and] at hgB
            simp only [incident_edges, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hgB with h | h <;> rw [h] <;> simp
        have hBK : B = K i j := Finset.Subset.antisymm hsub (hKsub i j)
        have hnn : 0 ≤ ∑ e ∈ K i j, u i e := Finset.sum_nonneg fun e _ => hu i e
        rw [hBK]; linarith
    · rw [if_neg hc]
      by_cases hc' : cut j i
      · have hij := cut_ne _ _ hc'
        have hBji : B = edges_between ends j i := propm_edges_between_symm ends i j
        have hs : ∑ e ∈ B, (if σ e = i then u i e else 0) =
            ∑ e ∈ B, u i e - ∑ e ∈ K j i, u i e := by
          rw [← propm_sum_ite_mem B (K j i) (hBji ▸ hKsub j i), ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun e he => ?_
          rw [key j i e hc' (hBji ▸ he)]
          by_cases hk : e ∈ K j i <;> simp [hk, hij]
        have h1 := hKh j i
        rw [← hBji] at h1
        have h2 := Finset.sum_sdiff (f := u i) (hBji ▸ hKsub j i : K j i ⊆ B)
        rw [hs]; linarith
      · have hempty : ∀ e ∈ B, False := by
          intro e he
          simp only [hB, edges_between, Finset.mem_filter, Finset.mem_univ, true_and] at he
          rcases he with h | h
          · have := total _ _ (hloop e) (hTe e)
            rw [h] at this; rcases this with h' | h'
            · exact hc h'
            · exact hc' h'
          · have := total _ _ (hloop e) (hTe e)
            rw [h] at this; rcases this with h' | h'
            · exact hc' h'
            · exact hc h'
        rw [Finset.sum_eq_zero fun e he => (hempty e he).elim,
          Finset.sum_eq_zero fun e he => (hempty e he).elim]
        norm_num
  have hsum : ∑ e ∈ incident_edges ends i, (u i e - 2 * if σ e = i then u i e else 0) ≤ 2 * d := by
    rw [propm_sum_incident ends hloop i]
    calc ∑ j, ∑ e ∈ edges_between ends i j, (u i e - 2 * if σ e = i then u i e else 0)
        ≤ ∑ j, (if cut i j then d else 0) := Finset.sum_le_sum fun j _ => hpair j
      _ = ((Finset.univ.filter fun j => cut i j).card : ℝ) * d := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * d := by
        have hcard : (Finset.univ.filter fun j => cut i j).card ≤ 2 :=
          (Finset.card_le_card fun j hj => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            exact hj.1).trans (hTd i)
        have : ((Finset.univ.filter fun j => cut i j).card : ℝ) ≤ 2 := by exact_mod_cast hcard
        nlinarith
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hval] at hsum
  unfold orientation_prop_share
  unfold additive_valuation at hsum ⊢
  linarith
