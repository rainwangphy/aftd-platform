import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationEdgeLowPortSelected
import AFTD.Kb.Tcs.CycleFactorHighColor

/-!
# truncation_maximal_factor_paths_see_four_colors

Topic: graphs   Node: 3a913f05414d

Provenance: helper lemma. Maximal unselected factor-path refinement for the OP-874 campaign.

Every maximal unselected factor-cycle path of at least four edges, bounded by selected factor edges, sees all four high colors on its incident factor edges.
-/

def truncation_maximal_factor_paths_see_four_colors
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (M : Finset (Sym2 V))
    (b : V → Bool) (c h : V → G.edgeSet → Fin 6) : Prop := ∀ (n : ℕ), ∀ [NeZero n], 3 ≤ n → ∀ p : Fin n → V, Function.Injective p →
    (∀ i, G.Adj (p i) (p (i+1))) →
    (∀ i, s(p i,p (i+1)) ∉ M) →
    ∀ (i : Fin n) (l : ℕ), 4 ≤ l → l < n →
    truncation_edge_low_port_selected G b h (p (i-1)) (p i) →
    truncation_edge_low_port_selected G b h (p (i + Fin.ofNat n l)) (p (i + Fin.ofNat n l + 1)) →
    (∀ j : Fin l, ¬ truncation_edge_low_port_selected G b h
      (p (i + Fin.ofNat n j.val)) (p (i + Fin.ofNat n j.val + 1))) →
    ∀ k : Fin 4, ∃ j : Fin (l+2), ∃ e : G.edgeSet,
      (e : Sym2 V) = s(p (i-1 + Fin.ofNat n j.val),p (i + Fin.ofNat n j.val)) ∧
      c (p (i-1 + Fin.ofNat n j.val)) e = cycle_factor_high_color k
