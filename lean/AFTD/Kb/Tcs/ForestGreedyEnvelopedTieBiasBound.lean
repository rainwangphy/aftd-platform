import AFTD.Prelude
import AFTD.Kb.Tcs.ForestGreedyLawEnveloped
import AFTD.Kb.Tcs.ForestCarpoolTailEnvelope
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# forest_greedy_enveloped_tie_bias_bound

Topic: online_algorithms   Node: 5340658d7d90

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

For an enveloped fixed-parity law and a fair coin, the probability of a greedy increase from a positive discrepancy j is bounded by the larger of the envelope at j+1 and the average of its values at j and j+2.
-/

theorem forest_greedy_enveloped_tie_bias_bound (β : Type) [Fintype β] [Nonempty β]
    (Y : β → ℤ) (hY : forest_greedy_law_enveloped β Y) (j : ℕ) (hj : 1 ≤ j) :
  (((Finset.univ.filter (fun p : β × Bool =>
    (j : ℤ) < Y p.1 ∨ ((j : ℤ) = Y p.1 ∧ p.2 = true))).card : ℝ) /
    (Fintype.card (β × Bool) : ℝ)) ≤
  max (forest_carpool_tail_envelope (j + 1))
    ((forest_carpool_tail_envelope j + forest_carpool_tail_envelope (j + 2)) / 2) := by
  classical
  let above : Finset β := Finset.univ.filter (fun b => (j : ℤ) < Y b)
  let equal : Finset β := Finset.univ.filter (fun b => (j : ℤ) = Y b)
  let lo : Finset β := Finset.univ.filter (fun b => (j : ℤ) ≤ Y b)
  let hi : Finset β := Finset.univ.filter (fun b => ((j + 2 : ℕ) : ℤ) ≤ Y b)
  let fav : Finset (β × Bool) := Finset.univ.filter (fun p =>
    (j : ℤ) < Y p.1 ∨ ((j : ℤ) = Y p.1 ∧ p.2 = true))
  have hdis : Disjoint above equal := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have ha' : (j : ℤ) < Y a := (Finset.mem_filter.mp ha).2
    have hb' : (j : ℤ) = Y a := (Finset.mem_filter.mp hb).2
    omega
  have hevent : fav = (above ×ˢ (Finset.univ : Finset Bool)) ∪ (equal ×ˢ {true}) := by
    ext p
    rcases p with ⟨b, c⟩
    simp [fav, above, equal, Finset.mem_product]
  have hprod_dis : Disjoint (above ×ˢ (Finset.univ : Finset Bool)) (equal ×ˢ {true}) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have ha : p.1 ∈ above := (Finset.mem_product.mp hp).1
    have hb : p.1 ∈ equal := (Finset.mem_product.mp hq).1
    exact (Finset.disjoint_left.mp hdis) ha hb
  have hfav : fav.card = 2 * above.card + equal.card := by
    rw [hevent, Finset.card_union_of_disjoint hprod_dis]
    simp [Finset.card_product, Nat.mul_comm]
  have hlo : lo = above ∪ equal := by
    ext b
    simp only [lo, above, equal, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hlo_card : lo.card = above.card + equal.card := by
    rw [hlo, Finset.card_union_of_disjoint hdis]
  have hp : (0 : ℝ) < Fintype.card β := by exact_mod_cast (Fintype.card_pos (α := β))
  have hpc : (0 : ℝ) < Fintype.card (β × Bool) := by
    exact_mod_cast (Fintype.card_pos (α := β × Bool))
  obtain ⟨parity, hparity⟩ := hY.1
  have htail := hY.2.2
  by_cases hzero : equal.card = 0
  · have hzeroR : (equal.card : ℝ) = 0 := by exact_mod_cast hzero
    have hfavR : (fav.card : ℝ) = 2 * (above.card : ℝ) := by exact_mod_cast (show fav.card = 2 * above.card by omega)
    have habove : above = Finset.univ.filter (fun b => ((j + 1 : ℕ) : ℤ) ≤ Y b) := by
      ext b
      simp only [above, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_add, Nat.cast_one]
      omega
    have htail1 := htail (j + 1) (by omega)
    have hprob : (fav.card : ℝ) / Fintype.card (β × Bool) =
        (above.card : ℝ) / Fintype.card β := by
      rw [hfavR]
      simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
      field_simp [ne_of_gt hp]
    calc
      _ = (above.card : ℝ) / Fintype.card β := hprob
      _ ≤ forest_carpool_tail_envelope (j + 1) := by simpa [habove] using htail1
      _ ≤ _ := le_max_left _ _
  · have hex : ∃ b, b ∈ equal := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
    obtain ⟨b0, hb0⟩ := hex
    have hb0' : (j : ℤ) = Y b0 := (Finset.mem_filter.mp hb0).2
    have habove : above = hi := by
      ext b
      have hpar : Y b % 2 = (j : ℤ) % 2 := by rw [hparity b, ← hparity b0, ← hb0']
      simp only [above, hi, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_add,
        Nat.cast_ofNat]
      omega
    have hfav2 : fav.card = lo.card + hi.card := by rw [hlo_card, ← habove, hfav]; omega
    have hfavR : (fav.card : ℝ) = (lo.card : ℝ) + (hi.card : ℝ) := by exact_mod_cast hfav2
    have htail0 := htail j hj
    have htail2 := htail (j + 2) (by omega)
    have hprob : (fav.card : ℝ) / Fintype.card (β × Bool) =
        ((lo.card : ℝ) / Fintype.card β + (hi.card : ℝ) / Fintype.card β) / 2 := by
      rw [hfavR]
      simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
      field_simp [ne_of_gt hp] <;> ring
    calc
      _ = ((lo.card : ℝ) / Fintype.card β + (hi.card : ℝ) / Fintype.card β) / 2 := hprob
      _ ≤ (forest_carpool_tail_envelope j + forest_carpool_tail_envelope (j + 2)) / 2 := by
        have h0 : (lo.card : ℝ) / Fintype.card β ≤ forest_carpool_tail_envelope j := by simpa [lo] using htail0
        have h2 : (hi.card : ℝ) / Fintype.card β ≤ forest_carpool_tail_envelope (j + 2) := by simpa [hi] using htail2
        linarith
      _ ≤ _ := le_max_right _ _
