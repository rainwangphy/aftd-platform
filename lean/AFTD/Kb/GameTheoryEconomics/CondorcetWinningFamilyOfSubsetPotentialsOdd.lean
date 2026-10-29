import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetOrderingScoreLeSubsetPotential
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_winning_family_of_subset_potentials_odd

Topic: social_choice   Node: f3277740a16e

Provenance: helper lemma. IN-341 generic verification helper for the OP-19 odd-electorate route and the known odd-three-to-universal-four reduction. It weakens the certificate threshold to a non-strict half only when the electorate is odd. No universal certificate construction, new dimension bound, or research advance is claimed. Original strict definition: https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf .

Fix a relation R on the candidates. Suppose every outside-challenger selector whose roots are R-related to all committee members has natural claim weights of positive total and a natural subset potential with all local removal inequalities and full-set cost at most half the total weight. Then every positive odd electorate whose strict pairwise-majority edges are contained in R has a strict Condorcet winning committee in that family. Certificate existence remains a hypothesis. No additional properties of R are assumed; one may choose the actual majority tournament.
-/

open Finset

theorem condorcet_winning_family_of_subset_potentials_odd
    (m q : ℕ) (S : Fin q → Finset (Fin m)) (R : Fin m → Fin m → Prop)
    (hcert : ∀ f : Fin q → Fin m, (∀ i, f i ∉ S i) →
      (∀ i,∀ c∈S i,R (f i) c) →
      ∃ (w : Fin q → ℕ) (H : Finset (Fin m) → ℕ),
        (∀ A : Finset (Fin m), ∀ a ∈ A,
          (∑ i, if f i=a ∧ S i ⊆ A.erase a then w i else 0)+H (A.erase a) ≤ H A) ∧
        0 < (∑ i,w i) ∧ 2*H univ ≤ ∑ i,w i) :
    ∀ (n : ℕ) (hn : 0<n) (hodd : Odd n) (P : Fin n → Equiv.Perm (Fin m))
      (hR : ∀ a b, n < 2*(univ.filter fun v => P v a < P v b).card → R a b),
      ∃ i,is_condorcet_winning_set P (S i) := by
  classical
  intro n hn hodd P hR
  by_contra hnone
  have hbad : ∀ i, ∃ a : Fin m, a ∉ S i ∧
      n ≤ 2*(univ.filter fun v => ∀ c ∈ S i, P v a < P v c).card := by
    intro i
    have hi : ¬is_condorcet_winning_set P (S i) := fun h => hnone ⟨i,h⟩
    unfold is_condorcet_winning_set at hi
    push_neg at hi
    exact hi
  choose f hf hmaj using hbad
  have hRel : ∀ i, ∀ c ∈ S i, R (f i) c := by
    intro i c hc
    apply hR
    have hsub : (univ.filter fun v => ∀ b ∈ S i, P v (f i) < P v b) ⊆
        (univ.filter fun v => P v (f i) < P v c) := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hv c hc
    have hcard := Finset.card_le_card hsub
    have hm := hmaj i
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨w, H, hstep, hpos, hH⟩ := hcert f hf hRel
  let score : Fin n → ℕ := fun v => ∑ i, if ∀ c ∈ S i, P v (f i) < P v c then w i else 0
  have hid : (∑ v, score v) =
      ∑ i, w i * (univ.filter fun v => ∀ c ∈ S i, P v (f i) < P v c).card := by
    dsimp only [score]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  have hscore : ∀ v, score v ≤ H univ := fun v =>
    condorcet_ordering_score_le_subset_potential m q S f w H hstep (P v)
  have hupp : 2 * (∑ v, score v) ≤ n * (∑ i, w i) := by
    have h1 : (∑ v, score v) ≤ n * H univ := by
      calc (∑ v, score v) ≤ ∑ _v : Fin n, H univ := Finset.sum_le_sum (fun v _ => hscore v)
        _ = n * H univ := by simp
    calc 2 * (∑ v, score v) ≤ 2 * (n * H univ) := Nat.mul_le_mul_left 2 h1
      _ = n * (2 * H univ) := by ring
      _ ≤ n * (∑ i, w i) := Nat.mul_le_mul_left n hH
  have hlow : (n+1) * (∑ i, w i) ≤ 2 * (∑ v, score v) := by
    rw [hid]
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hm := hmaj i
    obtain ⟨k, hk⟩ := hodd
    have h1 : n+1 ≤ 2*(univ.filter fun v => ∀ c ∈ S i, P v (f i) < P v c).card := by omega
    have h2 := Nat.mul_le_mul_right (w i) h1
    calc (n+1) * w i ≤ (2*(univ.filter fun v => ∀ c ∈ S i, P v (f i) < P v c).card) * w i := h2
      _ = 2 * (w i * (univ.filter fun v => ∀ c ∈ S i, P v (f i) < P v c).card) := by ring
  have hle : (n+1) * (∑ i, w i) ≤ n * (∑ i, w i) := le_trans hlow hupp
  have := Nat.le_of_mul_le_mul_right hle hpos
  omega
