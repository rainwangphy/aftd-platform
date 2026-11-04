import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAlphaMmsChores
import AFTD.Kb.GameTheoryEconomics.IsEf1Chores
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# ef1_implies_two_sub_one_div_n_mms_chores

Topic: fair_division   Node: d0ca09142bc4

Provenance: helper lemma. arXiv:2611.00432, Theorem 3.2

For any n ≥ 2 agents with nonnegative additive costs over m indivisible chores, any EF1 allocation satisfies (2 - 1/n)-MMS.
-/

private lemma ef1_implies_two_sub_one_div_n_mms_chores_item_le_mms {m n : ℕ} (hn : 1 ≤ n)
    (u : Fin m → ℝ) (hu : ∀ d, 0 ≤ u d) (e : Fin m) : u e ≤ chore_maximin_share n u := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simp only [chore_maximin_share]
  refine le_ciInf (fun P => ?_)
  have hbdd : BddAbove (Set.range fun k : Fin n => additive_valuation u (bundle_of P k)) :=
    (Set.finite_range _).bddAbove
  refine le_trans ?_ (le_ciSup hbdd (P e))
  have hmem : e ∈ bundle_of P (P e) := by simp [bundle_of]
  have := Finset.single_le_sum (f := u) (fun d _ => hu d) hmem
  simpa [additive_valuation] using this

private lemma ef1_implies_two_sub_one_div_n_mms_chores_mms_nonneg {m n : ℕ} (hn : 1 ≤ n)
    (u : Fin m → ℝ) (hu : ∀ d, 0 ≤ u d) : 0 ≤ chore_maximin_share n u := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simp only [chore_maximin_share]
  refine le_ciInf (fun P => ?_)
  have hbdd : BddAbove (Set.range fun k : Fin n => additive_valuation u (bundle_of P k)) :=
    (Set.finite_range _).bddAbove
  refine le_trans ?_ (le_ciSup hbdd ⟨0, hn⟩)
  simp only [additive_valuation]
  exact Finset.sum_nonneg (fun d _ => hu d)

private lemma ef1_implies_two_sub_one_div_n_mms_chores_sum_le_mms {m n : ℕ} (hn : 1 ≤ n)
    (u : Fin m → ℝ) : (∑ d, u d) ≤ (n : ℝ) * chore_maximin_share n u := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hle : (∑ d, u d) / n ≤ chore_maximin_share n u := by
    simp only [chore_maximin_share]
    refine le_ciInf (fun P => ?_)
    have hbdd : BddAbove (Set.range fun k : Fin n => additive_valuation u (bundle_of P k)) :=
      (Set.finite_range _).bddAbove
    have hsum : ∑ k, additive_valuation u (bundle_of P k) = ∑ d, u d := by
      have := Finset.sum_fiberwise (Finset.univ : Finset (Fin m)) P u
      simpa [bundle_of, additive_valuation] using this
    have h2 : ∑ k : Fin n, additive_valuation u (bundle_of P k)
        ≤ (⨆ k, additive_valuation u (bundle_of P k)) * (n:ℝ) := by
      calc ∑ k : Fin n, additive_valuation u (bundle_of P k)
          ≤ ∑ _k : Fin n, (⨆ k, additive_valuation u (bundle_of P k)) :=
            Finset.sum_le_sum (fun k _ => le_ciSup hbdd k)
        _ = (⨆ k, additive_valuation u (bundle_of P k)) * (n:ℝ) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    rw [div_le_iff₀ hnpos]
    linarith [hsum ▸ h2]
  calc (∑ d, u d) = (n:ℝ) * ((∑ d, u d) / n) := by field_simp
    _ ≤ (n:ℝ) * chore_maximin_share n u :=
        mul_le_mul_of_nonneg_left hle (le_of_lt hnpos)

private lemma ef1_implies_two_sub_one_div_n_mms_chores_fiber_sum {m n : ℕ} (u : Fin m → ℝ)
    (σ : Fin m → Fin n) :
    ∑ j : Fin n, additive_valuation u (bundle_of σ j) = ∑ d : Fin m, u d := by
  have := Finset.sum_fiberwise (Finset.univ : Finset (Fin m)) σ u
  simpa [bundle_of, additive_valuation] using this

private lemma ef1_implies_two_sub_one_div_n_mms_chores_main {m n : ℕ} (hn1 : 1 ≤ n)
    (u : Fin m → ℝ) (hu : ∀ d, 0 ≤ u d) (σ : Fin m → Fin n) (i : Fin n)
    (hef1 : ∀ j, additive_valuation u (bundle_of σ i) ≤ additive_valuation u (bundle_of σ j) ∨
      ∃ e ∈ bundle_of σ i, additive_valuation u (bundle_of σ i) - u e ≤ additive_valuation u (bundle_of σ j)) :
    additive_valuation u (bundle_of σ i) ≤ (2 - 1/(n:ℝ)) * chore_maximin_share n u := by
  have hnn : 0 ≤ chore_maximin_share n u := ef1_implies_two_sub_one_div_n_mms_chores_mms_nonneg hn1 u hu
  have hTM : (∑ d : Fin m, u d) ≤ (n:ℝ) * chore_maximin_share n u :=
    ef1_implies_two_sub_one_div_n_mms_chores_sum_le_mms hn1 u
  have hfib := ef1_implies_two_sub_one_div_n_mms_chores_fiber_sum (n := n) u σ
  have hperj : ∀ j ∈ (Finset.univ.erase i : Finset (Fin n)),
      additive_valuation u (bundle_of σ i) ≤ additive_valuation u (bundle_of σ j) + chore_maximin_share n u := by
    intro j _
    rcases hef1 j with h | ⟨e, _, hle⟩
    · linarith
    · have h1 : u e ≤ chore_maximin_share n u := ef1_implies_two_sub_one_div_n_mms_chores_item_le_mms hn1 u hu e
      linarith
  have hsumerase : ∑ j ∈ Finset.univ.erase i, additive_valuation u (bundle_of σ j)
      = (∑ d : Fin m, u d) - additive_valuation u (bundle_of σ i) := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun j => additive_valuation u (bundle_of σ j)) (Finset.mem_univ i)
    rw [hfib] at h
    linarith
  have hcard : ((Finset.univ.erase i : Finset (Fin n)).card : ℝ) = (n:ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    push_cast [Nat.cast_sub hn1]
    ring
  have hstep : ((n:ℝ) - 1) * additive_valuation u (bundle_of σ i)
      ≤ ((∑ d : Fin m, u d) - additive_valuation u (bundle_of σ i))
        + ((n:ℝ) - 1) * chore_maximin_share n u := by
    have h := Finset.sum_le_sum (s := (Finset.univ.erase i : Finset (Fin n))) hperj
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard, hsumerase] at h
    exact h
  have hmain : (n:ℝ) * additive_valuation u (bundle_of σ i)
      ≤ (2*(n:ℝ) - 1) * chore_maximin_share n u := by linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
  have hrw : (2 - 1/(n:ℝ)) * chore_maximin_share n u
      = ((2*(n:ℝ) - 1) * chore_maximin_share n u) / (n:ℝ) := by
    field_simp
  rw [hrw]
  rw [le_div_iff₀ hn0]
  linarith

/-- EF1 implies (2 - 1/n)-MMS for nonnegative additive chores. -/
theorem ef1_implies_two_sub_one_div_n_mms_chores (n m : ℕ) [NeZero n] (hn : 2 ≤ n) (c : Fin n → Fin m → ℝ) (hc : ∀ i d, 0 ≤ c i d) (σ : Fin m → Fin n) (hef1 : is_ef1_chores c σ) : is_alpha_mms_chores (2 - 1 / (n : ℝ)) c σ := by
  intro i
  exact ef1_implies_two_sub_one_div_n_mms_chores_main (by omega) (c i) (hc i) σ i (hef1 i)
