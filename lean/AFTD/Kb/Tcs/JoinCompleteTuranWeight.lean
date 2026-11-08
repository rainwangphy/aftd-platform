import AFTD.Prelude

/-!
# join_complete_turan_weight

Topic: graphs   Node: c720bfcfea1a

Provenance: formalization of a published result. Source: arXiv:2610.41371 Eq. (5)

The edge weighting function assigning rational weights (ℚ) to unordered pairs e : Sym2 (Fin a ⊕ Fin (n - a)): weight 2 / (r * (r - 1) : ℚ) if both endpoints lie in Fin a (via Sum.inl), weight 1 / ((r - 1) : ℚ) if one endpoint lies in Fin a and the other in Fin (n - a) (via Sum.inr), and weight 0 if both endpoints lie in Fin (n - a).
-/

/-- The edge weighting w_a on the join graph G_a = K_a ∨ T_{r-1}(n-a). -/
def join_complete_turan_weight (n r a : ℕ) (e : Sym2 (Fin a ⊕ Fin (n - a))) : ℚ :=
  Sym2.lift ⟨fun u v =>
    match u, v with
    | Sum.inl _, Sum.inl _ => 2 / (r * (r - 1) : ℚ)
    | Sum.inl _, Sum.inr _ => 1 / ((r - 1) : ℚ)
    | Sum.inr _, Sum.inl _ => 1 / ((r - 1) : ℚ)
    | Sum.inr _, Sum.inr _ => 0,
    by
      intro u v
      cases u <;> cases v <;> rfl
  ⟩ e
