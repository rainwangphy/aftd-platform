import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MenuScore
import AFTD.Kb.GameTheoryEconomics.IsMaximalAccepted
import AFTD.Kb.GameTheoryEconomics.MenuAccepted
import AFTD.Kb.GameTheoryEconomics.DelegationMenu

/-!
# principal_payoff_ge_menu_score

Topic: mechanism_design   Node: 905f612dfa68

Provenance: formalization of a published result. Source: arXiv:2611.33095 (Improved Downward-Closed Delegation Bounds), Lemma 2.1. The knowledge-base menu lets acceptance depend on the whole principal value vector, which includes the paper's menus depending on x_S; best responses are quantified over all of them, covering any tie-breaking.

Let E be a finite set and F a nonempty downward-closed family of finite subsets of E. Let M be a deterministic delegation menu, x : E → ℝ nonnegative principal values and y : E → ℝ strictly positive agent values. The agent either abstains, giving both parties 0, or submits a report S in F; if M accepts S at x, the agent receives y(S) = Σ_{i∈S} y_i and the principal x(S) = Σ_{i∈S} x_i, otherwise both receive 0. Suppose the agent's choice is a best response: its agent utility is at least 0 (abstaining) and at least the agent utility of every report in F. Then the principal's payoff is at least the score of M at x, the infimum of x(S) over the reports S that are inclusion-maximal among the nonempty reports in F accepted by M at x (the infimum of the empty set being 0).
-/

open Classical in
theorem principal_payoff_ge_menu_score {E : Type*} [Fintype E] [DecidableEq E]
    (F : Set (Finset E)) (hF : F.Nonempty)
    (hdown : ∀ S T : Finset E, S ∈ F → T ⊆ S → T ∈ F)
    (M : DelegationMenu E) (x y : E → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 < y i)
    (report : Option (Finset E)) (hfeas : ∀ S, report = some S → S ∈ F)
    (habstain : 0 ≤ report.elim 0 (fun S => if M.accepts S x then ∑ i ∈ S, y i else 0))
    (hbest : ∀ T ∈ F,
      (if M.accepts T x then ∑ i ∈ T, y i else 0) ≤
        report.elim 0 (fun S => if M.accepts S x then ∑ i ∈ S, y i else 0)) :
    menu_score M F x ≤
      report.elim 0 (fun S => if M.accepts S x then ∑ i ∈ S, x i else 0) := by
  have hpos : ∀ T : Finset E, T.Nonempty → 0 < ∑ i ∈ T, y i :=
    fun T hT => Finset.sum_pos (fun i _ => hy i) hT
  have hnonneg : 0 ≤ report.elim 0 (fun S => if M.accepts S x then ∑ i ∈ S, x i else 0) := by
    rcases report with _ | S
    · simp
    · simp only [Option.elim]
      split_ifs
      · exact Finset.sum_nonneg (fun i _ => hx i)
      · exact le_refl 0
  by_cases hA : ∃ S, S ∈ menu_accepted M F x
  · obtain ⟨S, hSF, hSne, hSacc⟩ := hA
    have h1 := hbest S hSF
    rw [if_pos hSacc] at h1
    have h1' := lt_of_lt_of_le (hpos S hSne) h1
    rcases report with _ | R
    · simp at h1'
    · simp only [Option.elim] at h1' hbest ⊢
      by_cases hR : M.accepts R x
      · rw [if_pos hR] at h1' hbest ⊢
        have hRne : R.Nonempty := by
          rcases R.eq_empty_or_nonempty with h | h
          · rw [h, Finset.sum_empty] at h1'; exact absurd h1' (lt_irrefl 0)
          · exact h
        have hRA : R ∈ menu_accepted M F x := ⟨hfeas R rfl, hRne, hR⟩
        have hmax : is_maximal_accepted M F x R := by
          refine ⟨hRA, fun T hT hRT => ?_⟩
          by_contra hTR
          have hss : R ⊂ T := Finset.ssubset_iff_subset_ne.2 ⟨hRT, fun h => hTR (h ▸ le_refl _)⟩
          obtain ⟨i, hiT, hiR⟩ := Finset.exists_of_ssubset hss
          have hlt : ∑ i ∈ R, y i < ∑ i ∈ T, y i :=
            Finset.sum_lt_sum_of_subset hRT hiT hiR (hy i) (fun j _ _ => (hy j).le)
          have := hbest T hT.1
          rw [if_pos hT.2.2] at this
          linarith
        unfold menu_score
        apply csInf_le
        · exact ⟨0, fun r ⟨S', _, hr⟩ => hr ▸ Finset.sum_nonneg (fun i _ => hx i)⟩
        · exact ⟨R, hmax, rfl⟩
      · rw [if_neg hR] at h1'; exact absurd h1' (lt_irrefl _)
  · have hempty : {r : ℝ | ∃ S, is_maximal_accepted M F x S ∧ r = ∑ i ∈ S, x i} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨S, hS, _⟩
      exact hA ⟨S, hS.1⟩
    unfold menu_score
    rw [hempty, Real.sInf_empty]
    exact hnonneg
