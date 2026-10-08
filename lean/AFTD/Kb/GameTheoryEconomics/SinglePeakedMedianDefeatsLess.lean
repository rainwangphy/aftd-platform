import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSinglePeaked
import AFTD.Kb.Tcs.V

/-!
# single_peaked_median_defeats_less

Topic: social_choice   Node: 2a1caadc86a0

Provenance: helper lemma. Black (1948), The Decisions of a Committee Using a Special Majority

Under single-peaked preferences with asymmetric preferences, if strictly more than half of the voters have peak at least m, then for any alternative y < m, the number of voters preferring y to m is strictly less than the number preferring m to y.
-/

/-- Under single-peaked preferences, an alternative strictly to the left of a right-majority median is majority defeated. -/
theorem single_peaked_median_defeats_less {V A : Type*} [Fintype V] [LinearOrder A]
    (P : V → A → A → Prop) [∀ v, DecidableRel (P v)]
    (hasymm : ∀ v x y, P v x y → ¬ P v y x)
    (peak : V → A) (hsp : ∀ v, is_single_peaked (P v) (peak v))
    (m : A) (hm : Fintype.card V < 2 * (Finset.filter (fun v => m ≤ peak v) Finset.univ).card)
    (y : A) (hym : y < m) :
    (Finset.filter (fun v => P v y m) Finset.univ).card < (Finset.filter (fun v => P v m y) Finset.univ).card := by
  classical
  set Sy := Finset.filter (fun v => P v y m) Finset.univ
  set Sm := Finset.filter (fun v => P v m y) Finset.univ
  set Speak := Finset.filter (fun v => m ≤ peak v) Finset.univ
  have hsub : Speak ⊆ Sm := by
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨hv.1, ?_⟩
    apply hsp v y m
    left
    exact ⟨hym, hv.2⟩
  have hcard_sub : Speak.card ≤ Sm.card := Finset.card_le_card hsub
  have hdisj : Disjoint Sy Sm := by
    rw [Finset.disjoint_filter]
    intro v _ hp
    exact hasymm v y m hp
  have hsum : Sy.card + Sm.card ≤ Fintype.card V := by
    have := Finset.card_le_univ (Sy ∪ Sm)
    rw [Finset.card_union_of_disjoint hdisj] at this
    exact this
  omega
