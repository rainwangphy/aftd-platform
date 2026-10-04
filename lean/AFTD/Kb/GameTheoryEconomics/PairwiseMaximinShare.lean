import AFTD.Prelude

/-!
# pairwise_maximin_share

Topic: fair_division   Node: 7675fe8d2c79

The maximin share of a valuation when the items U are split into two bundles: the maximum over T inside U of min(v(T), v(U - T)).
-/

/-- The maximin share of a valuation when the items `U` are split between two agents: the share an agent has in the instance restricted to two bundles (arXiv:2502.02815, Def. 11). -/
noncomputable def pairwise_maximin_share {m : ℕ} (v : Finset (Fin m) → ℝ)
    (U : Finset (Fin m)) : ℝ :=
  ⨆ T : {T : Finset (Fin m) // T ⊆ U}, min (v T) (v (U \ T))
