import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolThresholdA
import AFTD.Kb.Tcs.CarpoolSlack
import AFTD.Kb.Tcs.CarpoolEdgeCrosses
import AFTD.Kb.Tcs.CarpoolThresholdADiff
import AFTD.Kb.Tcs.CarpoolSlackEmpty
import AFTD.Kb.Tcs.CarpoolDeltaSum
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# carpool_backward_step_slack_increase

Topic: online_algorithms   Node: bb1cc968cf4e

Provenance: formalization of a published result. Source: arXiv:2611.00388 Lemma 4.1

For natural numbers n and T, an integer D, trajectory d : ℕ → Fin n → ℤ, and receiver/sender functions a, b : ℕ → Fin n satisfying for all t with 1 ≤ t and t ≤ T that a t ≠ b t, for all v, d t v = d (t - 1) v + (if v = a t then 1 else if v = b t then -1 else 0), and d t (a t) - d t (b t) ≤ 29: if 1 ≤ t, t ≤ T, S : Finset (Fin n) is nonempty, and carpool_edge_crosses (a t) (b t) S, then there exists a finite subset S' : Finset (Fin n) such that (S' = S ∨ S' = insert (b t) S ∨ S' = S \ {a t}), carpool_slack D (d (t - 1)) S' ≥ carpool_slack D (d t) S + 1, and (carpool_slack D (d t) S ≥ 0 → S'.Nonempty).
-/

/-- Lemma 4.1 in arXiv:2611.00388: potential increase along backward steps in carpooling. -/
theorem carpool_backward_step_slack_increase
    (n T : ℕ) (D : ℤ)
    (d : ℕ → Fin n → ℤ) (a b : ℕ → Fin n)
    (hab : ∀ t, 1 ≤ t → t ≤ T → a t ≠ b t)
    (hstep : ∀ t v, 1 ≤ t → t ≤ T →
      d t v = d (t - 1) v + (if v = a t then 1 else if v = b t then -1 else 0))
    (hgap : ∀ t, 1 ≤ t → t ≤ T → d t (a t) - d t (b t) ≤ 29)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (hcross : carpool_edge_crosses (a t) (b t) S) :
    ∃ S' : Finset (Fin n),
      (S' = S ∨ S' = insert (b t) S ∨ S' = S \ {a t}) ∧
      carpool_slack D (d (t - 1)) S' ≥ carpool_slack D (d t) S + 1 ∧
      (carpool_slack D (d t) S ≥ 0 → S'.Nonempty) := by
  have ht : a t ≠ b t := hab t ht1 htT
  have hsum : ∀ U : Finset (Fin n),
      ∑ i ∈ U, d (t - 1) i =
        ∑ i ∈ U, d t i - (if a t ∈ U then (1:ℤ) else 0) + (if b t ∈ U then (1:ℤ) else 0) := by
    intro U
    have hpt : ∀ i ∈ U, d (t-1) i = d t i - (if i = a t then (1:ℤ) else if i = b t then -1 else 0) := by
      intro i _
      have h := hstep t i ht1 htT
      linarith
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
    have hsplit : ∀ i : Fin n, (if i = a t then (1:ℤ) else if i = b t then -1 else 0) =
        (if i = a t then (1:ℤ) else 0) + (if i = b t then (-1:ℤ) else 0) := by
      intro i
      by_cases h1 : i = a t
      · subst h1; simp [ht]
      · simp [h1]
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
    split_ifs <;> simp
  unfold carpool_edge_crosses at hcross
  rcases hcross with ⟨haS, hbS⟩ | ⟨hbS, haS⟩
  · -- case: a t ∈ S, b t ∉ S
    have hk : 1 ≤ S.card := by have := Finset.card_pos.mpr hS; omega
    have hAt : ∑ i ∈ S, d (t-1) i = ∑ i ∈ S, d t i - 1 := by
      have h := hsum S
      rw [if_pos haS, if_neg hbS] at h
      linarith
    have hbt : d (t-1) (b t) = d t (b t) + 1 := by
      have h := hstep t (b t) ht1 htT
      rw [if_neg (Ne.symm ht), if_pos rfl] at h
      linarith
    have hSt : ∑ i ∈ insert (b t) S, d (t-1) i = ∑ i ∈ S, d t i + d t (b t) := by
      rw [Finset.sum_insert hbS, hAt, hbt]; ring
    have hSa : ∑ i ∈ S \ {a t}, d (t-1) i = ∑ i ∈ S \ {a t}, d t i := by
      have h := hsum (S \ {a t})
      have ha' : a t ∉ S \ {a t} := by simp
      have hb' : b t ∉ S \ {a t} := by
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        rintro ⟨hbs, hba⟩; exact hbS hbs
      rw [if_neg ha', if_neg hb'] at h
      linarith
    have hcardminus : (S \ {a t}).card = S.card - 1 := by
      rw [Finset.sdiff_singleton_eq_erase]
      exact Finset.card_erase_of_mem haS
    have hSminus_t : ∑ i ∈ S \ {a t}, d t i = ∑ i ∈ S, d t i - d t (a t) := by
      rw [Finset.sdiff_singleton_eq_erase]
      have h := Finset.sum_erase_add S (fun i => d t i) haS
      linarith
    have hcardplus : (insert (b t) S).card = S.card + 1 := Finset.card_insert_of_notMem hbS
    have hplus : carpool_slack D (d (t-1)) (insert (b t) S) =
        carpool_slack D (d t) S + (d t (b t) - (carpool_threshold_A D (S.card + 1) - carpool_threshold_A D S.card)) := by
      simp only [carpool_slack]
      rw [hSt, hcardplus]
      ring
    have hminus : carpool_slack D (d (t-1)) (S \ {a t}) =
        carpool_slack D (d t) S + (- d t (a t) + (carpool_threshold_A D S.card - carpool_threshold_A D (S.card - 1))) := by
      simp only [carpool_slack]
      rw [hSa, hcardminus, hSminus_t]
      ring
    have hdelta : (d t (b t) - (carpool_threshold_A D (S.card + 1) - carpool_threshold_A D S.card))
        + (- d t (a t) + (carpool_threshold_A D S.card - carpool_threshold_A D (S.card - 1))) ≥ 1 := by
      have h := carpool_delta_sum D (d t (a t)) (d t (b t)) S.card hk (hgap t ht1 htT)
      simpa using h
    by_cases hp : (d t (b t) - (carpool_threshold_A D (S.card + 1) - carpool_threshold_A D S.card)) ≥ 1
    · have hle : carpool_slack D (d (t-1)) (insert (b t) S) ≥ carpool_slack D (d t) S + 1 := by
        rw [hplus]; linarith
      exact ⟨insert (b t) S, Or.inr (Or.inl rfl), hle, fun _ => Finset.insert_nonempty (b t) S⟩
    · have hm : (- d t (a t) + (carpool_threshold_A D S.card - carpool_threshold_A D (S.card - 1))) ≥ 1 := by
        linarith
      have hle : carpool_slack D (d (t-1)) (S \ {a t}) ≥ carpool_slack D (d t) S + 1 := by
        rw [hminus]; linarith
      refine ⟨S \ {a t}, Or.inr (Or.inr rfl), hle, ?_⟩
      intro hs
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      rw [he, carpool_slack_empty] at hle
      linarith
  · -- case: b t ∈ S, a t ∉ S
    have hAt : ∑ i ∈ S, d (t-1) i = ∑ i ∈ S, d t i + 1 := by
      have h := hsum S
      rw [if_neg haS, if_pos hbS] at h
      linarith
    refine ⟨S, Or.inl rfl, ?_, fun _ => hS⟩
    simp only [carpool_slack]
    rw [hAt]
    ring_nf
    linarith
