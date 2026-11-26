import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsFef1
import AFTD.Kb.GameTheoryEconomics.IsStrongFef1
import AFTD.Kb.GameTheoryEconomics.IsHereditary
import AFTD.Kb.GameTheoryEconomics.IsTarget
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.Charity

/-!
# exists_fef1_not_strong_fef1_one_agent

Topic: fair_division   Node: fd138469396e

Provenance: helper lemma. arXiv:2611.34488, Proposition 2.4

There exists an instance with one agent, nonnegative additive valuation, unit-size goods under a budget constraint (hereditary family of bundles of size at most B), and an allocation that is FEF1 but fails strong FEF1.
-/

/-- FEF1 does not imply strong FEF1, even for one agent with unit sizes under budget constraints. -/
theorem exists_fef1_not_strong_fef1_one_agent :
    ∃ (m : ℕ) (v : Fin 1 → Fin m → ℝ) (_hv : ∀ i g, 0 ≤ v i g)
      (B : ℝ) (A : Fin 1 → Finset (Fin m)),
    let F : Fin 1 → Set (Finset (Fin m)) := fun _ => {S | (S.card : ℝ) ≤ B}
    (∀ i, is_hereditary (F i)) ∧
    is_fef1 v F A ∧ ¬ is_strong_fef1 v F A := by
  refine ⟨5, fun _ g => if g = 0 then 100 else 51, ?_, 2, fun _ => {0}, ?_⟩
  · intro i g
    change (0:ℝ) ≤ (if g = 0 then 100 else 51)
    split_ifs <;> norm_num
  · dsimp only
    have key : ∀ S : Finset (Fin 5), (0 : Fin 5) ∉ S →
        additive_valuation (fun g : Fin 5 => if g = 0 then 100 else 51) S = 51 * (S.card : ℝ) := by
      intro S hS
      unfold additive_valuation
      have h : ∀ j ∈ S, (fun g : Fin 5 => if g = 0 then 100 else 51) j = (51 : ℝ) := by
        intro j hj
        have hj0 : j ≠ 0 := fun h => hS (h ▸ hj)
        simp [hj0]
      rw [Finset.sum_congr rfl h]
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine ⟨?_, ?_⟩
      · simp
      · intro S T hS hTS
        simp only [Set.mem_ofPred_eq] at hS ⊢
        have h : (T.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hTS
        linarith
    · intro i D htarget T hTsub hTne hTmem
      have hTcard : (T.card : ℝ) ≤ 2 := hTmem
      have hD : D = charity (fun _ : Fin 1 => ({0} : Finset (Fin 5))) := by
        rcases htarget with ⟨j, hji, hDj⟩ | hD
        · exact absurd (Subsingleton.elim j i) hji
        · exact hD
      have h0D : (0 : Fin 5) ∉ D := by rw [hD]; decide
      have h0T : (0 : Fin 5) ∉ T := fun h => h0D (hTsub h)
      obtain ⟨g, hgT⟩ := hTne
      refine ⟨g, hgT, ?_⟩
      have h0erase : (0 : Fin 5) ∉ T.erase g := fun h => h0T (Finset.mem_of_mem_erase h)
      rw [key (T.erase g) h0erase]
      have hA : additive_valuation ((fun _ : Fin 1 => fun g : Fin 5 => if g = 0 then 100 else 51) i) ((fun _ => ({0} : Finset (Fin 5))) i) = 100 := by
        simp [additive_valuation]
      rw [hA]
      have hcard : (T.erase g).card ≤ 1 := by
        have hTc : T.card ≤ 2 := by exact_mod_cast hTcard
        rw [Finset.card_erase_of_mem hgT]
        omega
      have : ((T.erase g).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith
    · intro hstrong
      have htarget : is_target (fun _ : Fin 1 => ({0} : Finset (Fin 5))) 0 (charity (fun _ : Fin 1 => ({0} : Finset (Fin 5)))) := Or.inr rfl
      have hne : (charity (fun _ : Fin 1 => ({0} : Finset (Fin 5)))).Nonempty := by decide
      obtain ⟨g, hgD, huniv⟩ := hstrong 0 (charity (fun _ : Fin 1 => ({0} : Finset (Fin 5)))) htarget hne
      have hcard3 : ((charity (fun _ : Fin 1 => ({0} : Finset (Fin 5)))).erase g).card = 3 := by
        rw [Finset.card_erase_of_mem hgD]
        have h4 : (charity (fun _ : Fin 1 => ({0} : Finset (Fin 5)))).card = 4 := by decide
        omega
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := (charity (fun _ : Fin 1 => ({0} : Finset (Fin 5)))).erase g) (n := 2) (by rw [hcard3]; norm_num)
      have hTmem : T ∈ ({S : Finset (Fin 5) | (S.card : ℝ) ≤ 2} : Set (Finset (Fin 5))) := by
        show (T.card : ℝ) ≤ 2
        rw [hTcard]; norm_num
      have hTnot : (0 : Fin 5) ∉ T := by
        intro h
        have h1 : (0 : Fin 5) ∈ charity (fun _ : Fin 1 => ({0} : Finset (Fin 5))) := Finset.mem_of_mem_erase (hTsub h)
        exact absurd h1 (by decide)
      have hvT : additive_valuation ((fun _ : Fin 1 => fun g : Fin 5 => if g = 0 then 100 else 51) 0) T = 102 := by
        rw [key T hTnot, hTcard]; norm_num
      have hvA : additive_valuation ((fun _ : Fin 1 => fun g : Fin 5 => if g = 0 then 100 else 51) 0) ((fun _ => ({0} : Finset (Fin 5))) 0) = 100 := by
        simp [additive_valuation]
      have hle := huniv T hTsub hTmem
      rw [hvT, hvA] at hle
      norm_num at hle
