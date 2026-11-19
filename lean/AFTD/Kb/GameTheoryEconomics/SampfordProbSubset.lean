import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SampfordWeight
import AFTD.Kb.GameTheoryEconomics.SampfordTotalWeight

/-!
# sampfordProbSubset

Topic: social_choice   Node: 945ef8d6271d

Provenance: helper lemma. step towards sampford_consecutive_house_coupling_loss_delta_four

The Sampford sampling probability of a set S of parties given residues r with sum k: in the degenerate cases k = 0 and k = n it is the point mass at the empty set and at the full set respectively, and otherwise it is the normalized weight of S among all size-k subsets.
-/

open Classical in
/-- Sampford sampling probability of a subset of parties. -/
noncomputable def sampfordProbSubset {n : ℕ} (r : Fin n → ℝ) (k : ℕ) (S : Finset (Fin n)) : ℝ :=
  if k = 0 then (if S = ∅ then 1 else 0)
  else if k = n then (if S = Finset.univ then 1 else 0)
  else if S.card = k ∧ sampfordTotalWeight r k ≠ 0 then sampfordWeight r S / sampfordTotalWeight r k
  else 0
