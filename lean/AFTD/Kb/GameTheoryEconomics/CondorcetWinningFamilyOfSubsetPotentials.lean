import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetOrderingScoreLeSubsetPotential
import AFTD.Kb.GameTheoryEconomics.CondorcetWinningFamilyOfOrderingCertificates
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_winning_family_of_subset_potentials

Topic: social_choice   Node: 12b3db2b8c64

Provenance: helper lemma. IN-339 supporting step for the OP-19 campaign. Strict definition: Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . Related selector formulation: arXiv:2604.19851v2. These are verification and coalition-closure helpers; no new dimension bound or research advance is asserted.

If every outside-challenger selector for a finite committee family has nonnegative integer weights and a subset potential satisfying the local first-candidate removal inequalities, with twice the full-set potential strictly less than the total weight, then every positive finite electorate has a winning committee in the family. Universal certificate existence remains an explicit hypothesis.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_winning_family_of_subset_potentials
    (m q : ℕ) (S : Fin q → Finset (Fin m))
    (hcert : ∀ f : Fin q → Fin m, (∀ i, f i ∉ S i) →
      ∃ (w : Fin q → ℕ) (H : Finset (Fin m) → ℕ),
        (∀ A : Finset (Fin m), ∀ a ∈ A,
          (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) + H (A.erase a) ≤ H A) ∧
        2 * H univ < ∑ i, w i) :
    ∀ (n : ℕ) (hn : 0 < n) (P : Fin n → Equiv.Perm (Fin m)),
      ∃ i, is_condorcet_winning_set P (S i) := by
  apply condorcet_winning_family_of_ordering_certificates m q S
  intro f hf
  obtain ⟨w, H, hstep, hbound⟩ := hcert f hf
  refine ⟨w, ?_⟩
  intro σ
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 2
    (condorcet_ordering_score_le_subset_potential m q S f w H hstep σ)) hbound
