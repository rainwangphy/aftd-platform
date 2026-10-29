import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetOrderingCertificateExcludesCommonObstruction
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_winning_family_of_ordering_certificates

Topic: social_choice   Node: eefa8eb3ba6e

Provenance: helper lemma. Structural helpers for OP-19, following the strict definition in Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf , and the selector/ordering framework in arXiv:2604.19851v2. No new Condorcet dimension bound or research advance is claimed.

If every outsider selector on a finite committee family admits nonnegative integer weights such that every strict ranking satisfies claims of strictly less than half the total weight, every positive finite electorate has a Condorcet winning committee in that family. The universal certificate-existence hypothesis is explicit and unresolved for all triples.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem condorcet_winning_family_of_ordering_certificates
    (m q : ℕ) (S : Fin q → Finset (Fin m))
    (hcert : ∀ f : Fin q → Fin m, (∀ i, f i ∉ S i) →
      ∃ w : Fin q → ℕ, ∀ σ : Equiv.Perm (Fin m),
        2*(∑ i, if ∀ c ∈ S i, σ (f i) < σ c then w i else 0) < ∑ i, w i) :
    ∀ (n : ℕ) (hn : 0 < n) (P : Fin n → Equiv.Perm (Fin m)),
      ∃ i, is_condorcet_winning_set P (S i) := by
  classical
  intro n hn P
  by_contra hnone
  have hbad : ∀ i, ∃ a : Fin m, a ∉ S i ∧
      n ≤ 2*(univ.filter fun v => ∀ c ∈ S i, P v a < P v c).card := by
    intro i
    have hi : ¬is_condorcet_winning_set P (S i) := fun h => hnone ⟨i,h⟩
    unfold is_condorcet_winning_set at hi
    push_neg at hi
    exact hi
  choose f hf hmaj using hbad
  obtain ⟨w,hw⟩ := hcert f hf
  obtain ⟨i,hi⟩ := condorcet_ordering_certificate_excludes_common_obstruction n m q hn P S f w hw
  have := hmaj i
  omega
