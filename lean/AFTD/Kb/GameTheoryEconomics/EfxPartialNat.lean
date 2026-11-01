import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPartialNatUtility

/-!
# efx_partial_nat

Topic: fair_division   Node: f4d990638f05

Provenance: helper lemma. Arbitrary source-bundle padding of the OP-7 Pareto-maximal locked-good obstruction, experiments 11497 and 11498.

Natural EFX inequalities for a partial allocation whose last owner label denotes unallocated goods.
-/

def efx_partial_nat {n m : ℕ} (v : Fin n → Fin m → ℕ) (σ : Fin m → Fin (n+1)) : Prop := ∀ i j : Fin n, i ≠ j → ∀ g : Fin m, σ g = j.castSucc →
 (∑ h : Fin m, if σ h = j.castSucc then v i h else 0) ≤ efx_partial_nat_utility v σ i + v i g
