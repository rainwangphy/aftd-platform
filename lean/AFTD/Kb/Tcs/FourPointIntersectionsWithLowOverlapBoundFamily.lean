import AFTD.Prelude

/-!
# four_point_intersections_with_low_overlap_bound_family

Topic: combinatorics   Node: 150c6d4b4cad

Provenance: helper lemma. d=9 pair-intersection degree budget in the OP-1957 crossing-cut campaign.

Let F be a finite family of sets of at most six elements, each two of which meet in exactly four elements. Suppose every element of any pairwise intersection belongs to at most one further member of F. Then F has at most four members.
-/

theorem four_point_intersections_with_low_overlap_bound_family : ∀ {I V : Type*} [DecidableEq I] [DecidableEq V] (F : Finset I) (Q : I → Finset V),
    (∀ i ∈ F, (Q i).card ≤ 6) →
    (∀ i ∈ F, ∀ j ∈ F, i ≠ j → (Q i ∩ Q j).card = 4) →
    (∀ i ∈ F, ∀ j ∈ F, i ≠ j → ∀ q ∈ Q i ∩ Q j,
      (((F.erase i).erase j).filter (fun l => q ∈ Q l)).card ≤ 1) →
    F.card ≤ 4 := by
  intro I V instI instV F Q hsize hpair hload
  classical
  by_cases hsmall : F.card ≤ 1
  · omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
  let R := Q i ∩ Q j
  let T := (F.erase i).erase j
  have hR : R.card = 4 := hpair i hi j hj hij
  have hj' : j ∈ F.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hT : T.card + 2 = F.card := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi]
    omega
  have hother : ∀ l ∈ T, l ∈ F ∧ l ≠ i ∧ l ≠ j := by
    intro l hl
    simp only [T, Finset.mem_erase] at hl
    exact ⟨hl.2.2, hl.2.1, hl.1⟩
  have htwo : ∀ l ∈ T, 2 ≤ (R ∩ Q l).card := by
    intro l hl
    obtain ⟨hlF, hli, hlj⟩ := hother l hl
    have hil : i ≠ l := hli.symm
    have hcard := Finset.card_inter_add_card_union (Q i ∩ Q j) (Q i ∩ Q l)
    have hunion : ((Q i ∩ Q j) ∪ (Q i ∩ Q l)).card ≤ (Q i).card := by
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).1
      · exact (Finset.mem_inter.mp hx).1
    have heq : (Q i ∩ Q j) ∩ (Q i ∩ Q l) = R ∩ Q l := by
      ext x
      simp [R] <;> tauto
    rw [heq, hpair i hi j hj hij, hpair i hi l hlF hil] at hcard
    have hqi := hsize i hi
    omega
  have hswap : (∑ l ∈ T, (R ∩ Q l).card) =
      ∑ q ∈ R, (T.filter (fun l => q ∈ Q l)).card := by
    calc
      (∑ l ∈ T, (R ∩ Q l).card) =
          ∑ l ∈ T, ∑ q ∈ R, if q ∈ Q l then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [← Finset.card_filter]
            congr 1
      _ = ∑ q ∈ R, ∑ l ∈ T, if q ∈ Q l then 1 else 0 := Finset.sum_comm
      _ = ∑ q ∈ R, (T.filter (fun l => q ∈ Q l)).card := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.card_filter]
  have hlower := Finset.sum_le_sum htwo
  have hconstant : (∑ l ∈ T, (2 : ℕ)) = T.card * 2 := by simp
  rw [hconstant, hswap] at hlower
  have hupper : (∑ q ∈ R, (T.filter (fun l => q ∈ Q l)).card) ≤ ∑ q ∈ R, (1 : ℕ) := by
    apply Finset.sum_le_sum
    intro q hq
    exact hload i hi j hj hij q hq
  have hconstant' : (∑ q ∈ R, (1 : ℕ)) = R.card := by simp
  rw [hconstant', hR] at hupper
  omega
