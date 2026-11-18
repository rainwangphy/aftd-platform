import AFTD.Prelude

/-!
# borda_score

Topic: social_choice   Node: b183b4b265b6

Provenance: formalization of a published result. Source: Gehrlein and Fishburn (1978)

In an election with k voters and n candidates where each voter v has preferences given by a permutation P v : Equiv.Perm (Fin n), with smaller values indicating higher preference so that candidate y is ranked below c when P v c < P v y, the Borda score of candidate c is the sum over all voters v : Fin k of the number of candidates y : Fin n such that P v c < P v y.
-/

/-- Total Borda score of candidate c across k voters with preferences P over n candidates. -/
def borda_score (k n : ℕ) (P : Fin k → Equiv.Perm (Fin n)) (c : Fin n) : ℕ := ∑ v : Fin k, (Finset.univ.filter (fun y : Fin n => P v c < P v y)).card
