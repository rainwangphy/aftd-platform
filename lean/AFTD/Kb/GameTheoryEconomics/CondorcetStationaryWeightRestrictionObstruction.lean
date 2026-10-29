import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetOrderingScoreLeSubsetPotential

/-!
# condorcet_stationary_weight_restriction_obstruction

Topic: social_choice   Node: 23d6ee88bb98

Provenance: helper lemma. IN-339 auxiliary restriction diagnostic for OP-19. Exact integer data from experiments8322 and8326; related strict election definition from Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015). This refutes an extra stationarity restriction, not OP-19, and carries no research advance.

There exist an enumeration of all56 three-candidate subsets of eight candidates, an outside challenger for every triple, bijective member enumerators, and the insert-challenger/evict-one-member transition function, such that every nonnegative integer weighting stationary for this three-transition chain has total weight at most twice its identity-ranking claim score. Nevertheless this selector has unrestricted nonnegative integer weights and a natural-valued subset potential satisfying every local removal inequality with twice its full-set value strictly below the total weight.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

private def in339_data_s : Array (Finset (Fin 8)) := #[{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 1, 6}, {0, 1, 7}, {0, 2, 3}, {0, 2, 4}, {0, 2, 5}, {0, 2, 6}, {0, 2, 7}, {0, 3, 4}, {0, 3, 5}, {0, 3, 6}, {0, 3, 7}, {0, 4, 5}, {0, 4, 6}, {0, 4, 7}, {0, 5, 6}, {0, 5, 7}, {0, 6, 7}, {1, 2, 3}, {1, 2, 4}, {1, 2, 5}, {1, 2, 6}, {1, 2, 7}, {1, 3, 4}, {1, 3, 5}, {1, 3, 6}, {1, 3, 7}, {1, 4, 5}, {1, 4, 6}, {1, 4, 7}, {1, 5, 6}, {1, 5, 7}, {1, 6, 7}, {2, 3, 4}, {2, 3, 5}, {2, 3, 6}, {2, 3, 7}, {2, 4, 5}, {2, 4, 6}, {2, 4, 7}, {2, 5, 6}, {2, 5, 7}, {2, 6, 7}, {3, 4, 5}, {3, 4, 6}, {3, 4, 7}, {3, 5, 6}, {3, 5, 7}, {3, 6, 7}, {4, 5, 6}, {4, 5, 7}, {4, 6, 7}, {5, 6, 7}]
private def in339_s : Fin 56 → (Finset (Fin 8)) := fun i => in339_data_s[i.val]!
private def in339_data_f : Array (Fin 8) := #[7, 7, 7, 7, 7, 6, 7, 7, 7, 7, 6, 7, 7, 7, 6, 7, 7, 6, 7, 6, 5, 0, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 6, 0, 6, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4]
private def in339_f : Fin 56 → (Fin 8) := fun i => in339_data_f[i.val]!
private def in339_data_d : Array (Fin 3 → Fin 8) := #[![0, 1, 2], ![0, 1, 3], ![0, 1, 4], ![0, 1, 5], ![0, 1, 6], ![0, 1, 7], ![0, 2, 3], ![0, 2, 4], ![0, 2, 5], ![0, 2, 6], ![0, 2, 7], ![0, 3, 4], ![0, 3, 5], ![0, 3, 6], ![0, 3, 7], ![0, 4, 5], ![0, 4, 6], ![0, 4, 7], ![0, 5, 6], ![0, 5, 7], ![0, 6, 7], ![1, 2, 3], ![1, 2, 4], ![1, 2, 5], ![1, 2, 6], ![1, 2, 7], ![1, 3, 4], ![1, 3, 5], ![1, 3, 6], ![1, 3, 7], ![1, 4, 5], ![1, 4, 6], ![1, 4, 7], ![1, 5, 6], ![1, 5, 7], ![1, 6, 7], ![2, 3, 4], ![2, 3, 5], ![2, 3, 6], ![2, 3, 7], ![2, 4, 5], ![2, 4, 6], ![2, 4, 7], ![2, 5, 6], ![2, 5, 7], ![2, 6, 7], ![3, 4, 5], ![3, 4, 6], ![3, 4, 7], ![3, 5, 6], ![3, 5, 7], ![3, 6, 7], ![4, 5, 6], ![4, 5, 7], ![4, 6, 7], ![5, 6, 7]]
private def in339_d : Fin 56 → (Fin 3 → Fin 8) := fun i => in339_data_d[i.val]!
private def in339_data_next : Array (Fin 3 → Fin 56) := #[![25, 10, 5], ![29, 14, 5], ![32, 17, 5], ![34, 19, 5], ![35, 20, 5], ![35, 20, 4], ![39, 14, 10], ![42, 17, 10], ![44, 19, 10], ![45, 20, 10], ![45, 20, 9], ![48, 17, 14], ![50, 19, 14], ![51, 20, 14], ![51, 20, 13], ![53, 19, 17], ![54, 20, 17], ![54, 20, 16], ![55, 20, 19], ![55, 20, 18], ![55, 19, 18], ![6, 1, 0], ![7, 2, 0], ![8, 3, 0], ![9, 4, 0], ![45, 35, 24], ![11, 2, 1], ![12, 3, 1], ![13, 4, 1], ![51, 35, 28], ![15, 3, 2], ![16, 4, 2], ![54, 35, 31], ![18, 4, 3], ![55, 35, 33], ![55, 34, 33], ![26, 22, 21], ![27, 23, 21], ![28, 24, 21], ![29, 25, 21], ![30, 23, 22], ![31, 24, 22], ![32, 25, 22], ![33, 24, 23], ![34, 25, 23], ![35, 25, 24], ![40, 37, 36], ![41, 38, 36], ![42, 39, 36], ![43, 38, 37], ![44, 39, 37], ![45, 39, 38], ![49, 47, 46], ![50, 48, 46], ![51, 48, 47], ![54, 53, 52]]
private def in339_next : Fin 56 → (Fin 3 → Fin 56) := fun i => in339_data_next[i.val]!
private def in339_data_p : Array (ℕ) := #[0, 6, 12, 20, 20, 20, 13, 18, 24, 24, 24, 28, 33, 33, 33, 44, 44, 44, 55, 55, 55, 29, 33, 37, 37, 28, 38, 42, 42, 36, 48, 48, 45, 54, 55, 55, 56, 59, 59, 53, 62, 62, 58, 65, 63, 63, 82, 82, 78, 84, 81, 81, 105, 103, 103, 126]
private def in339_p : Fin 56 → (ℕ) := fun i => in339_data_p[i.val]!
private def in339_score : Fin 56 → ℕ := fun i => if ∀ b ∈ in339_s i, in339_f i < b then 1 else 0

private theorem in339_local : ∀ i, 3 * in339_p i + 70 ≤
    (∑ k : Fin 3, in339_p (in339_next i k)) + 139 * in339_score i := by
  decide +kernel

private theorem in339_family : ∀ i,
    (in339_s i).card = 3 ∧ in339_f i ∉ in339_s i ∧
      Function.Injective (in339_d i) ∧ in339_s i = univ.image (in339_d i) := by
  decide +kernel

private theorem in339_complete : ∀ T : Finset (Fin 8), T.card = 3 → ∃ i, in339_s i = T := by
  decide +kernel

private theorem in339_transition : ∀ i j,
    in339_s (in339_next i j) = insert (in339_f i) ((in339_s i).erase (in339_d i j)) := by
  decide +kernel

private theorem in339_certificate :
    ∃ (w : Fin 56 → ℕ) (H : Finset (Fin 8) → ℕ),
      (∀ A : Finset (Fin 8), ∀ a ∈ A,
        (∑ i, if in339_f i = a ∧ in339_s i ⊆ A.erase a then w i else 0) + H (A.erase a) ≤ H A) ∧
      2 * H univ < ∑ i, w i := by
  let w : Fin 56 → ℕ := fun i => if i = 18 ∨ i = 19 ∨ i = 20 then 1 else 0
  let H : Finset (Fin 8) → ℕ := fun A => if ({5, 6, 7} : Finset (Fin 8)) ⊆ A then 1 else 0
  refine ⟨w, H, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

private theorem in339_bound
    (next : Fin 56 → Fin 3 → Fin 56) (p s : Fin 56 → ℕ)
    (hlocal : ∀ i, 3 * p i + 70 ≤ (∑ k : Fin 3, p (next i k)) + 139 * s i)
    (w : Fin 56 → ℕ)
    (hstat : ∀ j, 3 * w j = ∑ i, ∑ k : Fin 3, if next i k = j then w i else 0) :
    (∑ i, w i) ≤ 2 * (∑ i, w i * s i) := by
  have hbalance : 3 * (∑ i, w i * p i) =
      ∑ i, w i * (∑ k : Fin 3, p (next i k)) := by
    calc
      3 * (∑ i, w i * p i) = ∑ j, (3 * w j) * p j := by
        simp only [Finset.mul_sum, Nat.mul_assoc]
      _ = ∑ j, (∑ i, ∑ k : Fin 3, if next i k = j then w i else 0) * p j := by
        apply sum_congr rfl
        intro j _
        rw [hstat j]
      _ = ∑ i, w i * (∑ k : Fin 3, p (next i k)) := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        simp only [ite_mul, zero_mul]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [Finset.mul_sum]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 56))) =>
    Nat.mul_le_mul_left (w i) (hlocal i))
  have hleft : (∑ i, w i * (3 * p i + 70)) =
      3 * (∑ i, w i * p i) + 70 * (∑ i, w i) := by
    calc
      _ = ∑ i, (3 * (w i * p i) + 70 * w i) := by
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hright : (∑ i, w i * ((∑ k : Fin 3, p (next i k)) + 139 * s i)) =
      (∑ i, w i * (∑ k : Fin 3, p (next i k))) +
        139 * (∑ i, w i * s i) := by
    calc
      _ = ∑ i, (w i * (∑ k : Fin 3, p (next i k)) + 139 * (w i * s i)) := by
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [sum_add_distrib, ← mul_sum]
  rw [hleft, hright] at hsum
  have hbound : 70 * (∑ i, w i) ≤ 139 * (∑ i, w i * s i) := by
    omega
  omega

theorem condorcet_stationary_weight_restriction_obstruction :
    ∃ (S : Fin 56 → Finset (Fin 8)) (f : Fin 56 → Fin 8)
      (d : Fin 56 → Fin 3 → Fin 8) (next : Fin 56 → Fin 3 → Fin 56),
      (∀ i, (S i).card = 3 ∧ f i ∉ S i ∧ Function.Injective (d i) ∧
        S i = univ.image (d i)) ∧
      (∀ T : Finset (Fin 8), T.card = 3 → ∃ i, S i = T) ∧
      (∀ i j, S (next i j) = insert (f i) ((S i).erase (d i j))) ∧
      (∀ w : Fin 56 → ℕ,
        (∀ j, 3 * w j = ∑ i, ∑ k : Fin 3, if next i k = j then w i else 0) →
        (∑ i, w i) ≤ 2 * ∑ i, if ∀ b ∈ S i, f i < b then w i else 0) ∧
      (∃ (w : Fin 56 → ℕ) (H : Finset (Fin 8) → ℕ),
        (∀ A : Finset (Fin 8), ∀ a ∈ A,
          (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) + H (A.erase a) ≤ H A) ∧
        2 * H univ < ∑ i, w i) := by
  refine ⟨in339_s, in339_f, in339_d, in339_next, in339_family, in339_complete,
    in339_transition, ?_, in339_certificate⟩
  intro w hstat
  have hb := in339_bound in339_next in339_p in339_score in339_local w hstat
  simpa only [in339_score, mul_ite, mul_one, mul_zero] using hb
