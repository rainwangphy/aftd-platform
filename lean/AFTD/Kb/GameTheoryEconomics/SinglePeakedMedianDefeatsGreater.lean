import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSinglePeaked

/-!
# single_peaked_median_defeats_greater

Topic: social_choice   Node: 4986bc9f338b

Provenance: helper lemma. Duncan Black, 'On the Rationale of Group Decision-making', Journal of Political Economy 56(1):23-34 (1948)

Under single-peaked preferences with asymmetric preferences, if strictly more than half of the voters have peak at most m, then for any alternative y > m, the number of voters preferring y to m is strictly less than the number preferring m to y.
-/

/-- Under single-peaked preferences, if strictly more than half of voters have peak at most m, then for any y > m strictly fewer voters prefer y to m than prefer m to y. -/
theorem single_peaked_median_defeats_greater {V A : Type*} [Fintype V] [LinearOrder A]
    (P : V → A → A → Prop) [∀ v, DecidableRel (P v)]
    (hasymm : ∀ v x y, P v x y → ¬ P v y x)
    (peak : V → A) (hsp : ∀ v, is_single_peaked (P v) (peak v))
    (m : A) (hm : Fintype.card V < 2 * (Finset.filter (fun v => peak v ≤ m) Finset.univ).card)
    (y : A) (hym : m < y) :
    (Finset.filter (fun v => P v y m) Finset.univ).card < (Finset.filter (fun v => P v m y) Finset.univ).card := by
  classical
  set S := Finset.filter (fun v => peak v ≤ m) Finset.univ
  set M := Finset.filter (fun v => P v m y) Finset.univ
  set Y := Finset.filter (fun v => P v y m) Finset.univ
  have hSM : S ⊆ M := by
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨hv.1, ?_⟩
    apply hsp v y m
    right
    exact ⟨hv.2, hym⟩
  have hS_card : S.card ≤ M.card := Finset.card_le_card hSM
  have hdisj : Disjoint Y S := by
    rw [Finset.disjoint_left]
    intro v hvY hvS
    rw [Finset.mem_filter] at hvY hvS
    have hPmy : P v m y := by
      apply hsp v y m
      right
      exact ⟨hvS.2, hym⟩
    exact hasymm v m y hPmy hvY.2
  have hle : Y.card + S.card ≤ Fintype.card V := by
    have hsub : Y ∪ S ⊆ Finset.univ := Finset.subset_univ (Y ∪ S)
    have hunion := Finset.card_union_of_disjoint hdisj
    have hcard := Finset.card_le_card hsub
    rw [hunion] at hcard
    rw [Finset.card_univ] at hcard
    exact hcard
  change Y.card < M.card
  have hm' : Fintype.card V < 2 * S.card := hm
  omega
