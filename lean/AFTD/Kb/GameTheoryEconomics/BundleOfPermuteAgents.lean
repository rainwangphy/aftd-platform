import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# bundle_of_permute_agents

Topic: fair_division   Node: 364c1999acfd

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01.

Reassigning every good by the inverse of an agent permutation makes the bundle of agent i equal to the old bundle of the permuted agent.
-/

open Function Finset

theorem bundle_of_permute_agents {m n : ℕ} (σ : Fin m → Fin n) (p : Equiv.Perm (Fin n))
    (i : Fin n) : bundle_of (fun g => p.symm (σ g)) i = bundle_of σ (p i) := by
  ext g
  simp [bundle_of, Equiv.symm_apply_eq]
