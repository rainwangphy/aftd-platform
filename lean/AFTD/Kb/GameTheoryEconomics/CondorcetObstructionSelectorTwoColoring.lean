import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetMutualBadOutsidersPartition

/-!
# condorcet_obstruction_selector_two_coloring

Topic: social_choice   Node: 4ab7101a66e2

Provenance: helper lemma. Structural helpers for OP-19, following the strict definition in Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf , and the selector/ordering framework in arXiv:2604.19851v2. No new Condorcet dimension bound or research advance is claimed.

For any positively sized electorate and any family of half-majority challenger claims, the graph joining mutually cross-member challenger claims admits a common two-coloring. The committee family can have any index type. This necessary structure alone does not imply a winning committee.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem condorcet_obstruction_selector_two_coloring
    (ι : Type*) (n m : ℕ) (hn : 0 < n) (P : Fin n → Equiv.Perm (Fin m))
    (S : ι → Finset (Fin m)) (f : ι → Fin m)
    (hbad : ∀ i, n ≤ 2 * (univ.filter fun v => ∀ c ∈ S i, P v (f i) < P v c).card) :
    ∃ color : ι → Bool, ∀ i j, f j ∈ S i → f i ∈ S j → color i ≠ color j := by
  classical
  let v₀ : Fin n := ⟨0,hn⟩
  let color : ι → Bool := fun i => decide (∀ c ∈ S i, P v₀ (f i) < P v₀ c)
  refine ⟨color,?_⟩
  intro i j hji hij
  have hp := (condorcet_mutual_bad_outsiders_partition n m P (S i) (S j) (f i) (f j)
    hji hij (hbad i) (hbad j)).2 v₀
  by_cases hi : ∀ c ∈ S i, P v₀ (f i) < P v₀ c
  · have hj : ¬∀ c ∈ S j, P v₀ (f j) < P v₀ c := hp.mp hi
    have hci : color i = true := by simpa only [color,decide_eq_true_eq] using hi
    have hcj : color j = false := by simpa only [color,decide_eq_false_iff_not] using hj
    rw [hci,hcj]
    decide
  · have hj : ∀ c ∈ S j, P v₀ (f j) < P v₀ c := by
      by_contra hh
      exact hi (hp.mpr hh)
    have hci : color i = false := by simpa only [color,decide_eq_false_iff_not] using hi
    have hcj : color j = true := by simpa only [color,decide_eq_true_eq] using hj
    rw [hci,hcj]
    decide
