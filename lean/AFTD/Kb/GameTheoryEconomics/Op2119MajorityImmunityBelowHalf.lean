import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SatisfiesMajorityCriterion
import AFTD.Kb.GameTheoryEconomics.IsKNomg
import AFTD.Kb.GameTheoryEconomics.VotingOptionSet
import AFTD.Kb.GameTheoryEconomics.OrderTop
import AFTD.Kb.GameTheoryEconomics.HasObviousGroupManipulation

/-!
# op_2119_majority_immunity_below_half

Topic: social_choice   Node: 6e9278bd5b5c

Provenance: formalization of a published result. Source: arXiv:2611.26224 Prop. 5, p. 11

Let $N$ be a finite set of voters and $A$ a finite, nonempty set of alternatives. If a social choice function $f : (N \to \text{LinearOrder } A) \to A$ satisfies the majority criterion, then for any $k \in \mathbb{N}$ with $2k < |N|$, $f$ is not obviously group manipulable by coalitions of size at most $k$ (that is, $f$ is $k$-NOMG).
-/

private lemma op_2119_majority_immunity_below_half_exists_order_top {A : Type*} [Fintype A] [Nonempty A] (x : A) :
    ∃ L : LinearOrder A, @order_top A _ _ L = x := by
  classical
  let n := Fintype.card A
  let h : A → ℕ := fun a => if a = x then n else (Fintype.equivFin A a).val
  have hinj : Function.Injective h := by
    intro a b hab
    by_cases ha : a = x
    · by_cases hb : b = x
      · exact ha.trans hb.symm
      · exfalso
        simp only [h, ha, hb, if_true, if_false] at hab
        have := (Fintype.equivFin A b).isLt
        omega
    · by_cases hb : b = x
      · exfalso
        simp only [h, ha, hb, if_true, if_false] at hab
        have := (Fintype.equivFin A a).isLt
        omega
      · simp only [h, ha, hb, if_false] at hab
        exact (Fintype.equivFin A).injective (Fin.ext hab)
  refine ⟨LinearOrder.lift' h hinj, ?_⟩
  rw [order_top]
  rw [@Finset.max'_eq_iff A (LinearOrder.lift' h hinj) Finset.univ Finset.univ_nonempty x]
  refine ⟨Finset.mem_univ x, ?_⟩
  intro b _
  change h b ≤ h x
  simp only [h, if_true]
  by_cases hb : b = x
  · simp [hb]
  · simp only [hb, if_false]
    have := (Fintype.equivFin A b).isLt
    omega

/-- Every voting rule satisfying the majority criterion is immune to obvious group manipulation by coalitions smaller than n/2. -/
theorem op_2119_majority_immunity_below_half {N A : Type*} [Fintype N] [Fintype A] [Nonempty A]
    (f : (N → LinearOrder A) → A) (h_maj : satisfies_majority_criterion f) (k : ℕ)
    (hk : 2 * k < Fintype.card N) : is_k_nomg f k := by
  classical
  intro C hCne hCle
  rintro ⟨P, P_dev, hman⟩
  have hC : 2 * C.card < Fintype.card N := by omega
  have key : ∀ Q : N → LinearOrder A, voting_option_set f C Q = Set.univ := by
    intro Q
    ext x
    simp only [voting_option_set, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨Lx, hLx⟩ := op_2119_majority_immunity_below_half_exists_order_top (A := A) x
    let P' : N → LinearOrder A := fun i => if i ∈ C then Q i else Lx
    refine ⟨P', ?_, ?_⟩
    · intro i hi
      simp only [P', if_pos hi]
    · apply h_maj P' x
      have hsub : Finset.univ \ C ⊆
          Finset.filter (fun i => @order_top A _ _ (P' i) = x) Finset.univ := by
        intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter] at hi ⊢
        simp only [P', if_neg hi, hLx]
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_univ_sdiff] at hcard
      have hcl := Finset.card_le_card (Finset.subset_univ C)
      omega
  have hT := key P
  have hF := key P_dev
  unfold has_obvious_group_manipulation at hman
  rcases hman with ⟨x, hxT, hxy⟩ | ⟨y, hyF, hyx⟩
  · have hx : x ∈ voting_option_set f C P := by rw [hT]; trivial
    obtain ⟨i, hi⟩ := hCne
    have hlt := hxy x (by rw [hF]; trivial) i hi
    exact @lt_irrefl A (P i).toPreorder x hlt
  · have hy : y ∈ voting_option_set f C P := by rw [hT]; trivial
    obtain ⟨i, hi⟩ := hCne
    have hlt := hyx y hy i hi
    exact @lt_irrefl A (P i).toPreorder y hlt
