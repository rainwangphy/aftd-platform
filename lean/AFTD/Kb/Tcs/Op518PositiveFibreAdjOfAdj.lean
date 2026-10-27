import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedTriple
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.IsRankThreeSignotope
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.PositiveFibreThree
import AFTD.Kb.Tcs.IsRankThreeUniformChirotope
import AFTD.Kb.Tcs.DiffersAtOne
import AFTD.Kb.Tcs.ChirotopeThreeGraph
import AFTD.Kb.Tcs.BruhatOrderThreeGraph

/-!
# op_518_positive_fibre_adj_of_adj

Topic: combinatorics   Node: 95300174975f

Provenance: formalization of a published result. Source: arXiv:2610.03808 Lemma 6.9(a)

For every natural number m > 0, and any functions u, v : OrderedTriple (Fin m) → ℤˣ that are rank-3 signotopes whose positive fibres are uniform rank-3 chirotopes on WithTop (Fin m), if u and v are adjacent in the higher Bruhat order bruhat_order_three_graph (Fin m), then their positive fibres are adjacent in chirotope_three_graph (WithTop (Fin m)).
-/

/-- An adjacent step in B(m, 2) maps to an adjacent step in the rank-3 chirotope mutation graph. -/
theorem op_518_positive_fibre_adj_of_adj (m : ℕ) (hm : 0 < m) (u v : OrderedTriple (Fin m) → ℤˣ) (hu : is_rank_three_signotope u) (hv : is_rank_three_signotope v) (hu_chi : is_rank_three_uniform_chirotope (positive_fibre_three u)) (hv_chi : is_rank_three_uniform_chirotope (positive_fibre_three v)) (h : (bruhat_order_three_graph (Fin m)).Adj ⟨u, hu⟩ ⟨v, hv⟩) : (chirotope_three_graph (WithTop (Fin m))).Adj ⟨positive_fibre_three u, hu_chi⟩ ⟨positive_fibre_three v, hv_chi⟩ := by
  have _ := hm
  change differs_at_one (positive_fibre_three u) (positive_fibre_three v)
  have h_diff : differs_at_one u v := h
  rcases h_diff with ⟨t₀, ht₀_ne, ht₀_uniq⟩
  refine ⟨⟨some t₀.a, some t₀.b, some t₀.c, WithTop.coe_lt_coe.mpr t₀.ab, WithTop.coe_lt_coe.mpr t₀.bc⟩, ?_, ?_⟩
  · intro h_eq
    apply ht₀_ne
    have h1 : positive_fibre_three u ⟨some t₀.a, some t₀.b, some t₀.c, WithTop.coe_lt_coe.mpr t₀.ab, WithTop.coe_lt_coe.mpr t₀.bc⟩ = u t₀ := rfl
    have h2 : positive_fibre_three v ⟨some t₀.a, some t₀.b, some t₀.c, WithTop.coe_lt_coe.mpr t₀.ab, WithTop.coe_lt_coe.mpr t₀.bc⟩ = v t₀ := rfl
    rw [← h1, ← h2, h_eq]
  · intro t ht
    rcases t with ⟨a, b, c, hab, hbc⟩
    rcases a with _ | a
    · exact (ht rfl).elim
    · rcases b with _ | b
      · exact (ht rfl).elim
      · rcases c with _ | c
        · exact (ht rfl).elim
        · have h_ne : u ⟨a, b, c, WithTop.coe_lt_coe.mp hab, WithTop.coe_lt_coe.mp hbc⟩ ≠
                      v ⟨a, b, c, WithTop.coe_lt_coe.mp hab, WithTop.coe_lt_coe.mp hbc⟩ := ht
          have h_eq : (⟨a, b, c, WithTop.coe_lt_coe.mp hab, WithTop.coe_lt_coe.mp hbc⟩ : OrderedTriple (Fin m)) = t₀ :=
            ht₀_uniq _ h_ne
          subst h_eq
          rfl
