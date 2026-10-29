import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# condorcet_ordering_certificate_excludes_common_obstruction

Topic: social_choice   Node: 623cfc153f5d

Provenance: helper lemma. Structural helpers for OP-19, following the strict definition in Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf , and the selector/ordering framework in arXiv:2604.19851v2. No new Condorcet dimension bound or research advance is claimed.

For any finite family of challenger claims with nonnegative integer weights, if in every strict ranking their total satisfied weight is strictly less than half the total weight, no positive finite electorate can give all these claims at least half support.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem condorcet_ordering_certificate_excludes_common_obstruction
    (n m q : ℕ) (hn : 0 < n) (P : Fin n → Equiv.Perm (Fin m))
    (S : Fin q → Finset (Fin m)) (f : Fin q → Fin m) (w : Fin q → ℕ)
    (hcert : ∀ σ : Equiv.Perm (Fin m),
      2 * (∑ i, if ∀ c ∈ S i, σ (f i) < σ c then w i else 0) < ∑ i, w i) :
    ∃ i, 2 * (univ.filter fun v => ∀ c ∈ S i, P v (f i) < P v c).card < n := by
  classical
  let score : Fin n → ℕ := fun v => ∑ i, if ∀ c ∈ S i, P v (f i) < P v c then w i else 0
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,mem_univ _⟩
  have hu := Finset.sum_lt_sum_of_nonempty hne (fun v _ => hcert (P v))
  have hu' : 2*(∑ v, score v) < n*(∑ i, w i) := by
    simpa only [score,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,card_univ,Fintype.card_fin] using hu
  have hid : (∑ v, score v) = ∑ i, w i * (univ.filter fun v => ∀ c ∈ S i, P v (f i) < P v c).card := by
    dsimp [score]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm]
  by_contra hnone
  have hbad : ∀ i, n ≤ 2*(univ.filter fun v => ∀ c ∈ S i, P v (f i) < P v c).card := by
    intro i
    by_contra hn'
    exact hnone ⟨i,by omega⟩
  have hl : (∑ i, w i)*n ≤ 2*(∑ v, score v) := by
    rw [hid,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := Nat.mul_le_mul_left (w i) (hbad i)
    nlinarith
  nlinarith
