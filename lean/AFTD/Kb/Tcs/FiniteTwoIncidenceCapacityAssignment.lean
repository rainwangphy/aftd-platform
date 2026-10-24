import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# finite_two_incidence_capacity_assignment

Topic: graphs   Node: 088f4198af85

Provenance: helper lemma. Helper for OP-494 in arXiv:2610.30174, following the additive-list coloring argument of arXiv:2302.02190v3, Corollary 5.3. Double-count incidences for every set of edges, apply finite matching to endpoint slots, and bound assignment fibers by the injective slot labels.

A finite incidence relation with two endpoints for every edge and at most d incident edges at every vertex, d at least two, admits an endpoint assignment with capacity d minus one.
-/

open scoped BigOperators

theorem finite_two_incidence_capacity_assignment
    {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (R : E → V → Prop) [DecidableRel R]
    (d : ℕ) (hd : 2 ≤ d)
    (he : ∀ e, (Finset.univ.filter (R e)).card = 2)
    (hv : ∀ v, (Finset.univ.filter (fun e => R e v)).card ≤ d) :
    ∃ f : E → V, (∀ e, R e (f e)) ∧
      ∀ v, (Finset.univ.filter (fun e => f e = v)).card ≤ d - 1 := by
  classical
  let Q : E → V × Fin (d - 1) → Prop := fun e p => R e p.1
  have hall : ∀ s : Finset E,
      s.card ≤ (Finset.univ.filter (fun p : V × Fin (d - 1) => ∃ e ∈ s, Q e p)).card := by
    intro s
    let U : Finset V := Finset.univ.filter (fun v => ∃ e ∈ s, R e v)
    have hrow (e : E) (hes : e ∈ s) :
        U.bipartiteAbove R e = Finset.univ.filter (R e) := by
      ext v
      simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_univ, true_and, U]
      exact ⟨And.right, fun h => ⟨⟨e, hes, h⟩, h⟩⟩
    have hcount : s.card * 2 ≤ U.card * d := by
      simpa only [smul_eq_mul] using
        (Finset.card_nsmul_le_card_nsmul (R := ℕ) R
          (s := s) (t := U) (m := 2) (n := d)
          (fun e hes => by rw [hrow e hes, he e]; norm_num)
          (fun v _ => (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))).trans (hv v)))
    have hd' : d ≤ 2 * (d - 1) := by omega
    have hbound : s.card ≤ U.card * (d - 1) := by
      have := Nat.mul_le_mul_left U.card hd'
      nlinarith
    have hslots : Finset.univ.filter (fun p : V × Fin (d - 1) => ∃ e ∈ s, Q e p) =
        U ×ˢ Finset.univ := by
      ext p
      simp [Q, U]
    rw [hslots, Finset.card_product]
    simpa using hbound
  obtain ⟨g, hginj, hg⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective Q).mp hall
  refine ⟨fun e => (g e).1, hg, ?_⟩
  intro v
  calc
    (Finset.univ.filter (fun e => (g e).1 = v)).card ≤
        (Finset.univ : Finset (Fin (d - 1))).card := by
      apply Finset.card_le_card_of_injOn (fun e => (g e).2)
      · intro e _; exact Finset.mem_univ _
      · intro e he' e' he'' h
        apply hginj
        apply Prod.ext
        · exact (Finset.mem_filter.mp he').2.trans (Finset.mem_filter.mp he'').2.symm
        · exact h
    _ = d - 1 := by simp
