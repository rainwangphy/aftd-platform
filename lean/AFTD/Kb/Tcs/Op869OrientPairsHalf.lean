import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op869_orient_pairs_half

Topic: online_algorithms   Node: 22b9d27dad6b

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.4: the orientation step used to produce two-sided colors.

Given finitely many marked pairs of distinct indices, there is a set of indices whose boundary crosses at least half the pairs, counting repetitions separately.
-/

open scoped symmDiff

theorem op869_orient_pairs_half {γ : Type} [DecidableEq γ] (m : ℕ)
    (C : Finset γ) (u v : γ → Fin m) (huv : ∀ c ∈ C, u c ≠ v c) :
    ∃ s : Finset (Fin m), C.card ≤ 2 * (C.filter (fun c =>
      (u c ∈ s ∧ v c ∉ s) ∨ (u c ∉ s ∧ v c ∈ s))).card := by
  classical
  let F : Finset (Finset (Fin m)) := Finset.univ
  let cross (s : Finset (Fin m)) (c : γ) : Prop :=
    (u c ∈ s ∧ v c ∉ s) ∨ (u c ∉ s ∧ v c ∈ s)
  let w (s : Finset (Fin m)) : ℕ := (C.filter (cross s)).card
  have hF : F.Nonempty := ⟨∅, by simp [F]⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image F w hF
  have hhalf (c : γ) (hc : c ∈ C) :
      2 * (F.filter (fun s => cross s c)).card = F.card := by
    have hflip (s : Finset (Fin m)) : cross (s ∆ {u c}) c ↔ ¬ cross s c := by
      simp only [cross, Finset.mem_symmDiff, Finset.mem_singleton]
      have hne : v c ≠ u c := Ne.symm (huv c hc)
      simp only [hne, not_false_eq_true, and_true, and_false, or_false, or_true, not_true_eq_false]
      tauto
    have hequal : (F.filter (fun s => cross s c)).card = (F.filter (fun s => ¬ cross s c)).card := by
      apply Finset.card_bij' (fun s _ => s ∆ {u c}) (fun s _ => s ∆ {u c})
      · intro s hs
        simp
      · intro s hs
        simp
      · intro s hs
        simp only [Finset.mem_filter] at hs ⊢
        exact ⟨by simp [F], by simpa [hflip] using hs.2⟩
      · intro s hs
        simp only [Finset.mem_filter] at hs ⊢
        exact ⟨by simp [F], by simpa [hflip] using hs.2⟩
    have htotal := Finset.card_filter_add_card_filter_not (s := F) (fun s => cross s c)
    omega
  have hsum : F.card * C.card = 2 * ∑ s ∈ F, w s := by
    calc
      F.card * C.card = ∑ c ∈ C, F.card := by simp [mul_comm]
      _ = ∑ c ∈ C, 2 * (F.filter (fun s => cross s c)).card := by
        apply Finset.sum_congr rfl
        intro c hc
        exact (hhalf c hc).symm
      _ = 2 * ∑ s ∈ F, w s := by
        have hcount (c : γ) : (F.filter (fun s => cross s c)).card =
            ∑ s ∈ F, if cross s c then 1 else 0 := by
          exact (Finset.sum_boole (R := ℕ) (fun s => cross s c) F).symm
        have hcount' (s : Finset (Fin m)) : w s =
            ∑ c ∈ C, if cross s c then 1 else 0 := by
          exact (Finset.sum_boole (R := ℕ) (fun c => cross s c) C).symm
        simp_rw [hcount, hcount', Finset.mul_sum]
        rw [Finset.sum_comm]
  refine ⟨s, ?_⟩
  have hbound : (∑ t ∈ F, w t) ≤ F.card * w s := by
    simpa using Finset.sum_le_card_nsmul F w (w s) (fun t ht => hmax t ht)
  have hpos : 0 < F.card := Finset.card_pos.mpr hF
  have : C.card ≤ 2 * w s := by nlinarith
  simpa [w, cross] using this
