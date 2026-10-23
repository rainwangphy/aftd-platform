import AFTD.Prelude

/-!
# efx_po_in_singleton_family

Topic: fair_division   Node: cfbc068370b1

Provenance: helper lemma. step towards efx_pareto_incompatible_pos_additive

An allocation of the 4-agent 8-good instance is in the singleton family if goods 0 and 1 have distinct owners and no other good is given to either of those two owners.
-/

/-- Allocation whose goods 0 and 1 are singletons with distinct owners. -/
abbrev efx_po_in_singleton_family (σ : Fin 8 → Fin 4) : Prop :=
  σ 0 ≠ σ 1 ∧ ∀ g : Fin 8, g ≠ 0 → g ≠ 1 → σ g ≠ σ 0 ∧ σ g ≠ σ 1
