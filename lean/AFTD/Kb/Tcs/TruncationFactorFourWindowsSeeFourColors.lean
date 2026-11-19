import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationEdgeLowPortSelected
import AFTD.Kb.Tcs.CycleFactorHighColor

/-!
# truncation_factor_four_windows_see_four_colors

Topic: graphs   Node: 7a42bdef1550

Provenance: helper lemma. Four-window completion on a matching cut in the OP-874 campaign.

Every unselected path of four consecutive factor edges sees all four high colors among its six incident factor edges.
-/

def truncation_factor_four_windows_see_four_colors
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (M : Finset (Sym2 V))
    (b : V → Bool) (c h : V → G.edgeSet → Fin 6) : Prop := ∀ (n : ℕ), ∀ [NeZero n], 5 ≤ n → ∀ p : Fin n → V, Function.Injective p →
    (∀ i, G.Adj (p i) (p (i+1))) →
    (∀ i, s(p i,p (i+1)) ∉ M) → ∀ i : Fin n,
    (∀ j : Fin 4, ¬ truncation_edge_low_port_selected G b h
      (p (i + Fin.ofNat n j.val)) (p (i + Fin.ofNat n j.val + 1))) →
    ∀ k : Fin 4, ∃ j : Fin 6, ∃ e : G.edgeSet,
      (e : Sym2 V) = s(p (i-1 + Fin.ofNat n j.val),p (i + Fin.ofNat n j.val)) ∧
      c (p (i-1 + Fin.ofNat n j.val)) e = cycle_factor_high_color k
