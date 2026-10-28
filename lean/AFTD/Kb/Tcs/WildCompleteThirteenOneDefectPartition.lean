import AFTD.Prelude
import AFTD.Kb.Tcs.WildCompleteThirteenOneSwapRepairObstruction
import AFTD.Kb.Tcs.WildNumberCompleteGraphUpperSubFourAddParity
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq

/-!
# wild_complete_thirteen_one_defect_partition

Topic: graphs   Node: 10fca7126c86

Provenance: helper lemma. First-moment helper for the finite n=13 case of OP-306. The seven cut sizes are 3,3,3,4,6,6,6. The total expected number of closed cut-color pairs is bounded by 17/11<2. This does not itself produce a seal-free partition, and the one-swap repair obstruction shows the missing step is substantive.

For every normalized minimum proper coloring of K_13, there exists a vertex permutation of the block partition 3+3+3+4 for which at most one pair consisting of one of the seven cuts up to complementation and a color is closed. The hypothesis gives a bijection m between colors and their unique missing vertices; E is exactly the set of closed cut-color pairs after the permutation.
-/

open scoped BigOperators Classical

private def wild_complete_thirteen_one_defect_partition_cut_bound (j : Fin 7) : ℕ :=
  (wsc_repair_cuts wsc_repair_blocks j).card.factorial *
  (13 / 2).choose ((wsc_repair_cuts wsc_repair_blocks j).card / 2) *
  (13 - (wsc_repair_cuts wsc_repair_blocks j).card).factorial

private lemma wild_complete_thirteen_one_defect_partition_sum_bound :
    13 * (∑ j : Fin 7, wild_complete_thirteen_one_defect_partition_cut_bound j) < 2 * Nat.factorial 13 := by
  decide

theorem wild_complete_thirteen_one_defect_partition
    (c : (⊤ : SimpleGraph (Fin 13)).lineGraph.Coloring (Fin 13)) (m : Fin 13 ≃ Fin 13)
    (hm : ∀ (i v : Fin 13), (∀ w (hvw : v ≠ w), c ⟨s(v,w),wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) :
    ∃ (σ : Equiv.Perm (Fin 13)) (E : Finset (Fin 7 × Fin 13)), E.card ≤ 1 ∧
      ∀ ji : Fin 7 × Fin 13, ji ∈ E ↔
        w279_closed c ji.2 ((wsc_repair_cuts wsc_repair_blocks ji.1).image σ) := by
  classical
  by_contra! h
  let Bad (σ : Equiv.Perm (Fin 13)) : Finset (Fin 7 × Fin 13) :=
    Finset.univ.filter (fun ji => w279_closed c ji.2 ((wsc_repair_cuts wsc_repair_blocks ji.1).image σ))
  have h2 : ∀ σ, 2 ≤ (Bad σ).card := by
    intro σ
    have hσ := h σ (Bad σ)
    by_contra! hlt
    obtain ⟨ji, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hσ (by omega)
    · simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      exact h2 h1
    · simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      exact h1 h2
  have h_sum_lower : 2 * Nat.factorial 13 ≤ ∑ σ : Equiv.Perm (Fin 13), (Bad σ).card := by
    have h_le := Finset.card_nsmul_le_sum (s := (Finset.univ : Finset (Equiv.Perm (Fin 13)))) (f := fun σ => (Bad σ).card) (n := 2) (fun σ _ => h2 σ)
    rw [nsmul_eq_mul, mul_comm, Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h_le
    exact h_le
  have h_sum_eq :
    (∑ σ : Equiv.Perm (Fin 13), (Bad σ).card) =
    ∑ j : Fin 7, ∑ i : Fin 13,
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin 13) =>
        w279_closed c i ((wsc_repair_cuts wsc_repair_blocks j).image σ))).card := by
    simp_rw [Bad, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have h_sum_upper :
    (∑ j : Fin 7, ∑ i : Fin 13,
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin 13) =>
        w279_closed c i ((wsc_repair_cuts wsc_repair_blocks j).image σ))).card) ≤
    ∑ j : Fin 7, ∑ i : Fin 13, wild_complete_thirteen_one_defect_partition_cut_bound j := by
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro i _
    exact w3_closed_event_card c m hm (wsc_repair_cuts wsc_repair_blocks j) i
  have h_sum_eval :
    (∑ j : Fin 7, ∑ _i : Fin 13, wild_complete_thirteen_one_defect_partition_cut_bound j) =
    13 * ∑ j : Fin 7, wild_complete_thirteen_one_defect_partition_cut_bound j := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    rfl
  have h_lt := wild_complete_thirteen_one_defect_partition_sum_bound
  omega
