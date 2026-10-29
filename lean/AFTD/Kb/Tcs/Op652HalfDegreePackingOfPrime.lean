import AFTD.Prelude
import AFTD.Kb.Tcs.CoprimeDivisorProgressionGraph
import AFTD.Kb.Tcs.CoprimeDivisorProgressionGraphDecidableAdj
import AFTD.Kb.Tcs.SimpleGraphHasEdgeDisjointPerfectMatchings
import AFTD.Kb.Tcs.Op652HalfDegreePackingOfMinDegreeLeTwo

/-!
# op_652_half_degree_packing_of_prime

Topic: graphs   Node: fb9f681b25f7

Provenance: helper lemma. arXiv:2610.37512

For any prime p and integers a, b with b > 0, if the coprime divisor progression graph B has a perfect matching, then B contains at least ⌈δ(B)/2⌉ pairwise edge-disjoint perfect matchings.
-/

/-- OP-652 holds for any prime p, as |D(p)| = 2 and ceil(delta/2) <= 1. -/
theorem op_652_half_degree_packing_of_prime (p : ℕ) (hp : p.Prime) (a b : ℤ) (hb : 0 < b)
    (hM : ∃ M : (coprime_divisor_progression_graph p a b).Subgraph, M.IsPerfectMatching) :
    simple_graph_has_edge_disjoint_perfect_matchings
      (coprime_divisor_progression_graph p a b)
      (((coprime_divisor_progression_graph p a b).minDegree + 1) / 2) := open SimpleGraph in by
  have hdeg : (coprime_divisor_progression_graph p a b).minDegree ≤ 2 := by
    have h1_mem : 1 ∈ p.divisors := Nat.one_mem_divisors.mpr hp.ne_zero
    let v : {d // d ∈ p.divisors} ⊕ {x // x ∈ (Finset.range p.divisors.card).image (fun (t : ℕ) => a + b * (t : ℤ))} :=
      Sum.inl ⟨1, h1_mem⟩
    have hdeg_le := (coprime_divisor_progression_graph p a b).minDegree_le_degree v
    apply le_trans hdeg_le
    change ((coprime_divisor_progression_graph p a b).neighborFinset v).card ≤ 2
    have hsub : (coprime_divisor_progression_graph p a b).neighborFinset v ⊆
        Finset.map ⟨Sum.inr, Sum.inr_injective⟩ Finset.univ := by
      intro w hw
      rw [mem_neighborFinset] at hw
      cases w with
      | inl d' =>
        exfalso
        revert hw
        simp [coprime_divisor_progression_graph, fromRel]
      | inr x =>
        rw [Finset.mem_map]
        exact ⟨x, Finset.mem_univ _, rfl⟩
    have hcard_le := Finset.card_le_card hsub
    apply le_trans hcard_le
    rw [Finset.card_map, Finset.card_univ, Fintype.card_coe]
    have himage_le := Finset.card_image_le (f := fun (t : ℕ) => a + b * (t : ℤ)) (s := Finset.range p.divisors.card)
    apply le_trans himage_le
    rw [Finset.card_range]
    rw [Nat.Prime.divisors hp]
    rw [Finset.card_pair hp.ne_one.symm]
  exact op_652_half_degree_packing_of_min_degree_le_two p hp.two_le a b hb hdeg hM
