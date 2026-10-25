import AFTD.Prelude

/-!
# ejr_support_density_bound

Topic: social_choice   Node: 47ddd1519841

Provenance: helper lemma. Supporting work for OP-22, arXiv:2007.01795, Q2, and the proposed max-group-density invariant in memory attempt 4342. These helpers neither settle full-chain existence nor refute the actual greedy rule. No research advance is claimed.

The finite supporter-density bound: for every candidate subset T, its undersatisfied supporter count times q is at most |T| times the number of voters. The proposed size-k invariant uses q=k+1.
-/

def ejr_support_density_bound {n m : ℕ} (A : Fin n → Finset (Fin m))
    (q : ℕ) (W : Finset (Fin m)) : Prop := ∀ T : Finset (Fin m),
    (Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ W).card < T.card).card * q ≤
      T.card * n
