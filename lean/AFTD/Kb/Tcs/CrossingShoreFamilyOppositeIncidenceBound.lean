import AFTD.Prelude

/-!
# crossing_shore_family_opposite_incidence_bound

Topic: graphs   Node: 9fe7365d567d

Provenance: helper lemma. OP-1957 crossing-shore structural reduction, session IN-1122.

For the displayed family of crossing shores with a selected shore meeting all others, the selected-root and opposite-shore cardinalities obey the stated degree-budget inequality.
-/

theorem crossing_shore_family_opposite_incidence_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (d t : ℕ) (S C F : Finset V) (hSC : Disjoint S C)
    (hF : F ⊆ C) (hS : S.card + 1 = d)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (Q W : V → Finset V)
    (hW : ∀ z ∈ F, W z ⊆ S)
    (hzQ : ∀ z ∈ F, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ F, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hcut : ∀ z ∈ F, ∀ z' ∈ F, (W z ∩ W z').Nonempty →
      (W z ∪ W z').card + (Q z ∩ Q z').card = d + 1)
    (z : V) (hz : z ∈ F) (hwt : (W z).card + t = d)
    (hmeets : ∀ z' ∈ F, (W z ∩ W z').Nonempty) :
    2 * F.card + (Q z).card ≤ (Q z).card * t + 2 := by
  classical
  have hint : ∀ r ∈ F, 2 ≤ (Q z ∩ Q r).card := by
    intro r hr
    have hsub : W z ∪ W r ⊆ S := Finset.union_subset (hW z hz) (hW r hr)
    have hc := Finset.card_le_card hsub
    have heq := hcut z hz r hr (hmeets r hr)
    omega
  have hlower : 2 * F.card + (Q z).card ≤
      (∑ r ∈ F, (Q z ∩ Q r).card) + 2 := by
    have hsum := Finset.sum_le_sum (s := F.erase z)
      (f := fun _ => 2) (g := fun r => (Q z ∩ Q r).card)
      (by intro r hr; exact hint r (Finset.mem_of_mem_erase hr))
    have hpos : 0 < F.card := Finset.card_pos.mpr ⟨z, hz⟩
    have herase : (F.erase z).card + 1 = F.card := by rw [Finset.card_erase_of_mem hz]; omega
    have hsplit := Finset.add_sum_erase F (fun r => (Q z ∩ Q r).card) hz
    have hsum' : 2 * (F.erase z).card ≤ ∑ r ∈ F.erase z, (Q z ∩ Q r).card := by
      simpa [Nat.mul_comm] using hsum
    simp only [Finset.inter_self] at hsplit
    omega
  have hdegree : ∀ q ∈ Q z, (F.filter (fun r => q ∈ Q r)).card ≤ t := by
    intro q hq
    let R := F.filter (fun r => q ∈ Q r)
    have hdis : Disjoint (W z) R := by
      apply Finset.disjoint_left.mpr
      intro a ha hr
      have haS := hW z hz ha
      have haF : a ∈ F := (Finset.mem_filter.mp (show a ∈ F.filter (fun r => q ∈ Q r) from hr)).1
      have haC := hF haF
      exact (Finset.disjoint_left.mp hSC) haS haC
    have hsub : W z ∪ R ⊆ H.neighborFinset q := by
      intro a ha
      rw [H.mem_neighborFinset]
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hcross z hz q hq a ha
      · have ha' := Finset.mem_filter.mp ha
        exact (hzQ a ha'.1 q ha'.2).symm
    have hc := (Finset.card_le_card hsub).trans (hmax q)
    rw [Finset.card_union_of_disjoint hdis] at hc
    change R.card ≤ t
    omega
  have hswap : (∑ r ∈ F, (Q z ∩ Q r).card) =
      ∑ q ∈ Q z, (F.filter (fun r => q ∈ Q r)).card := by
    calc
      (∑ r ∈ F, (Q z ∩ Q r).card) =
          ∑ r ∈ F, ∑ q ∈ Q z, if q ∈ Q r then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [← Finset.card_filter]
            congr 1
      _ = ∑ q ∈ Q z, ∑ r ∈ F, if q ∈ Q r then 1 else 0 := Finset.sum_comm
      _ = ∑ q ∈ Q z, (F.filter (fun r => q ∈ Q r)).card := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.card_filter]
  have hupper := Finset.sum_le_sum (s := Q z)
    (f := fun q => (F.filter (fun r => q ∈ Q r)).card) (g := fun _ => t) hdegree
  rw [← hswap] at hupper
  have hupper' : (∑ r ∈ F, (Q z ∩ Q r).card) ≤ (Q z).card * t := by
    simpa using hupper
  omega
