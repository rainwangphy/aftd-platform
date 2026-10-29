import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# condorcet_mutual_bad_outsiders_partition

Topic: social_choice   Node: 36f8d4e07e69

Provenance: helper lemma. Structural helpers for OP-19, following the strict definition in Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf , and the selector/ordering framework in arXiv:2604.19851v2. No new Condorcet dimension bound or research advance is claimed.

If two challenger claims are incompatible because each challenger lies in the other committee, and each has at least half the voter support, the electorate is even and their supporting voter coalitions are exact complements. This is a necessary condition, not a bound on committee size.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem condorcet_mutual_bad_outsiders_partition
    (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m))
    (S T : Finset (Fin m)) (a b : Fin m) (hba : b ∈ S) (hab : a ∈ T)
    (hS : n ≤ 2 * (univ.filter fun v => ∀ c ∈ S, P v a < P v c).card)
    (hT : n ≤ 2 * (univ.filter fun v => ∀ c ∈ T, P v b < P v c).card) :
    Even n ∧ ∀ v : Fin n,
      (∀ c ∈ S, P v a < P v c) ↔ ¬(∀ c ∈ T, P v b < P v c) := by
  let A := univ.filter fun v : Fin n => ∀ c ∈ S, P v a < P v c
  let B := univ.filter fun v : Fin n => ∀ c ∈ T, P v b < P v c
  change n ≤ 2*A.card at hS
  change n ≤ 2*B.card at hT
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvB
    have h₁ := (mem_filter.mp hvA).2 b hba
    have h₂ := (mem_filter.mp hvB).2 a hab
    exact (lt_asymm h₁ h₂)
  have hc : A.card+B.card ≤ n := by
    rw [← card_union_of_disjoint hd]
    simpa only [card_univ,Fintype.card_fin] using card_le_univ (A∪B)
  have heq : A.card+B.card=n := by omega
  have hfull : A∪B=univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    simpa only [card_univ,Fintype.card_fin,card_union_of_disjoint hd,heq] using Nat.le_refl n
  refine ⟨⟨A.card,by omega⟩,?_⟩
  intro v
  have hv : v ∈ A ↔ v ∉ B := by
    constructor
    · intro hA hB
      exact Finset.disjoint_left.mp hd hA hB
    · intro hB
      have hu : v ∈ A∪B := by rw [hfull]; exact mem_univ v
      rcases mem_union.mp hu with hA | hB'
      · exact hA
      · exact (hB hB').elim
  simpa only [A,B,mem_filter,mem_univ,true_and] using hv
