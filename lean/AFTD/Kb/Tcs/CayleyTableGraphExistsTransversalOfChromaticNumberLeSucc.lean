import AFTD.Prelude
import AFTD.Kb.Tcs.CayleyTableGraph
import AFTD.Kb.Tcs.CayleyTableGraphIndepSetCardLe

/-!
# cayley_table_graph_exists_transversal_of_chromatic_number_le_succ

Topic: combinatorics   Node: ef2ae9e9e1fb

Provenance: formalization of a published result. Source: arXiv:2611.13274 Proposition 1.2

If the chromatic number of the Cayley table graph of a finite group G is at most |G| + 1, then the Cayley table has a transversal (an independent set of cardinality |G|).
-/

/-- If the chromatic number of the Cayley table graph is at most |G| + 1, then the table contains a transversal. -/
theorem cayley_table_graph_exists_transversal_of_chromatic_number_le_succ
    (G : Type*) [Group G] [Fintype G]
    (h : (cayley_table_graph G).chromaticNumber ≤ Fintype.card G + 1) :
    ∃ s : Finset (G × G), (cayley_table_graph G).IsIndepSet (s : Set (G × G)) ∧ s.card = Fintype.card G := by
  classical
  have hcol : (cayley_table_graph G).Colorable (Fintype.card G + 1) :=
    SimpleGraph.chromaticNumber_le_iff_colorable.mp h
  obtain ⟨c⟩ := hcol
  set n := Fintype.card G with hn
  set g : Fin (n + 1) → Finset (G × G) := fun i => Finset.univ.filter (fun v => c v = i) with hg
  have hindep : ∀ i, (cayley_table_graph G).IsIndepSet (g i : Set (G × G)) := by
    intro i
    intro v hv w hw hne hadj
    simp only [hg, Finset.coe_filter, Finset.mem_univ, true_and] at hv hw
    have hthis := c.map_adj hadj
    have hne' : c v ≠ c w := hthis
    exact hne' (by rw [hv, hw])
  have hle : ∀ i, (g i).card ≤ n := by
    intro i
    have := cayley_table_graph_indep_set_card_le G (g i) (hindep i)
    simpa [hn] using this
  have hcard := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (G × G)))
    (t := (Finset.univ : Finset (Fin (n + 1)))) (f := c) (fun x _ => Finset.mem_univ _)
  have hsum : ∑ i : Fin (n + 1), (g i).card = n * n := by
    rw [← hcard, Finset.card_univ, Fintype.card_prod, hn]
  suffices hex : ∃ i, (g i).card = n by
    obtain ⟨i, hi⟩ := hex
    exact ⟨g i, hindep i, hi⟩
  by_contra hcon
  have hlt : ∀ i, (g i).card + 1 ≤ n := by
    intro i
    have h1 := hle i
    have h2 : (g i).card ≠ n := fun hh => hcon ⟨i, hh⟩
    omega
  have hstep : ∑ i : Fin (n+1), ((g i).card + 1) ≤ ∑ i : Fin (n+1), n :=
    Finset.sum_le_sum (fun i _ => hlt i)
  have hleft : ∑ i : Fin (n+1), ((g i).card + 1) = n*n + (n+1) := by
    rw [Finset.sum_add_distrib, hsum]
    simp
  have hright : ∑ i : Fin (n+1), n = (n+1)*n := by
    simp [Finset.sum_const]
  rw [hleft, hright] at hstep
  have hfin : n*n + (n+1) ≤ n*n + n := by
    calc n*n + (n+1) ≤ (n+1)*n := hstep
    _ = n*n + n := by ring
  omega
